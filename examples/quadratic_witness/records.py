"""Standalone exact quadratic witness record search. Python 3.11+, stdlib only."""
import argparse
import csv
import hashlib
import json
from math import isqrt
import os
from pathlib import Path
import struct
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MAX_UPPER = (1 << 128) - 1
INITIAL_UPPER = 10000
MAX_INTERVAL = 1 << 64
# The immediately preceding interval-capped format-2 writer is migratable.
LEGACY_RECORDS_SHA256 = '52cd82adcf92bf90a0ebbec9121cb9aa41496431047c25f5744ab0e8443835fe'
FORMAT1_HASHES = {
    'records.py': '22026a61571d217f964e9aa608ed9fb613be9ed1416bf254ff3ca43f66175fc7',
    'search.cpp': '2d42c8ed065557d83e09e7b17c59152a568bbeaa256ca26d5dda9b57d0336c26',
    'search.exe': 'eaaf4230b415aeda2cb728c5250881c511acf3f3f8bd583ae603e932c24b49a8'}
PREVIOUS_FORMAT3_SHA256 = '7ae810ce1fc0755dd8be12929238d69e9c9c26106a0b97a8956b770d1e5e1a4a'
PREVIOUS_FORMAT3_BASELINE_SHA256 = '515055bc92c2cdcb104da5e0eb5bc27aede9d45a6a774c7d63470a5d556e8e1a'
PREVIOUS_SEARCH_SHA256 = '30129d14c0d8a3cf26caa37ed9275450f81d75b67f89fc14d48edcde6659663d'


def next_upper(covered, target):
    """Grow small prefixes geometrically, but add at most 2^64 integers."""
    return min(target, covered * 16, covered + MAX_INTERVAL)


def primes():
    yield 3
    p = 5
    while True:
        if all(p % d for d in range(3, isqrt(p) + 1, 2)):
            yield p
        p += 2


def witness(n, kind):
    for p in primes():
        a = pow(n % p, (p - 1) // 2, p)
        if a == p - 1 or (kind == 'non_one' and a == 0):
            return p


def reference_minima(upper, kind):
    minima = {}
    for n in range(3, upper + 1, 2):
        if isqrt(n) ** 2 != n:
            minima.setdefault(witness(n, kind), n)
    return [{'n': n, 'witness': p} for p, n in sorted(minima.items())]


def record_rows(minima):
    rows, maximum = [], 0
    for row in sorted(minima, key=lambda row: row['n']):
        if row['witness'] > maximum:
            rows.append(dict(row))
            maximum = row['witness']
    return rows


def reference(upper, kind):
    return record_rows(reference_minima(upper, kind))


def prime_minimum_rows(minima):
    found = {row['witness']: row['n'] for row in minima}
    maximum = max(found, default=0)
    for p in primes():
        if p > maximum:
            break
        yield {'witness': p, 'n': found.get(p, '')}


def save(path, obj):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2) + '\n', encoding='utf-8')
    tmp.replace(path)


RESULT_SHARDS = 16
MAX_RESULT_BYTES = 64 << 20


def journal_rows(path, total):
    """Validate every committed frame, including empty chunks, exactly once."""
    seen = bytearray((total + 7) // 8)
    completed = 0
    for shard in range(RESULT_SHARDS):
        journal = path / f'results-{shard}.journal'
        if not journal.exists():
            continue
        with journal.open('rb') as f:
            while header := f.read(32):
                if len(header) != 32:
                    raise ValueError('incomplete result journal header; resume the engine')
                magic, chunk, size, checksum = struct.unpack('<8s3Q', header)
                if (magic != b'QWJNL001' or chunk >= total or
                        chunk % RESULT_SHARDS != shard or size > MAX_RESULT_BYTES):
                    raise ValueError('invalid result journal header')
                payload = f.read(size)
                if len(payload) != size:
                    raise ValueError('incomplete result journal frame; resume the engine')
                actual = 14695981039346656037
                for byte in header[8:24] + payload:
                    actual = ((actual ^ byte) * 1099511628211) & ((1 << 64) - 1)
                if checksum != actual:
                    raise ValueError('result journal checksum mismatch')
                mask = 1 << (chunk % 8)
                if seen[chunk // 8] & mask:
                    raise ValueError('duplicate result journal chunk')
                seen[chunk // 8] |= mask
                completed += 1
                for line in payload.decode('ascii').splitlines():
                    n, witness_value, count = map(int, line.split(','))
                    yield {'chunk': chunk, 'n': n, 'witness': witness_value, 'count': count}
    if completed != total:
        raise ValueError('missing result journal chunks')


def reduce_job(path, kind, threshold, upper, lower=1):
    """Require every chunk, and independently verify its reported minimum."""
    params = json.loads((path / 'branch.json').read_text())
    if (params['non_one'] != (kind == 'non_one') or
            params['threshold'] != threshold or
            int(params['upper_exclusive']) != upper + 1 or params['root_prime'] or
            int(params.get('lower_inclusive', '1')) != lower):
        raise ValueError('job parameters mismatch')
    data = (path / 'odd/done.bitmap').read_bytes()
    h = struct.unpack('<8s10Q', data[:88])
    total = h[2]
    if (h[0] != b'NEGRBM1\0' or h[1] != threshold or
            (h[-2] << 64 | h[-1]) != upper or
            len(data) != 88 + 8 * ((total + 63) // 64)):
        raise ValueError('invalid bitmap')
    done = int.from_bytes(data[88:], 'little')
    if done & ((1 << total) - 1) != (1 << total) - 1:
        raise ValueError('incomplete job')
    minima = {}
    for row in journal_rows(path / 'odd', total):
        n, p = row['n'], row['witness']
        if not (row['count'] > 0 and max(3, lower) <= n <= upper and n % 2 and
                isqrt(n) ** 2 != n and p >= threshold and witness(n, kind) == p):
            raise ValueError('invalid chunk minimum')
        minima[p] = min(minima.get(p, n), n)
    return minima


def publish(work, state):
    save(work / 'status.json', state)
    for kind, info in state['searches'].items():
        target = work / f'{kind}_records.csv'
        tmp = target.with_suffix('.csv.tmp')
        with tmp.open('w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=['n', 'witness'])
            writer.writeheader()
            writer.writerows(info['records'])
        tmp.replace(target)
        target = work / f'{kind}_prime_minima.csv'
        tmp = target.with_suffix('.csv.tmp')
        with tmp.open('w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=['witness', 'n'])
            writer.writeheader()
            writer.writerows(prime_minimum_rows(info['minima']))
        tmp.replace(target)


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    bounds = parser.add_mutually_exclusive_group()
    bounds.add_argument('--bits', type=int, default=None,
                        help='search odd n < 2^BITS; 1..128 (default: 64)')
    bounds.add_argument('--upper', type=int, help='inclusive decimal upper bound')
    parser.add_argument('--kind', choices=['both', 'negative', 'non_one'], default='both')
    parser.add_argument('--work-dir', type=Path, default=Path('witness-records-work'))
    parser.add_argument('--engine', type=Path, default=HERE / ('search.exe' if os.name == 'nt' else 'search'))
    parser.add_argument('--threads', type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument('--chunk-size', type=int, default=1 << 20)
    args = parser.parse_args(argv)
    if args.bits is not None and not 1 <= args.bits <= 128:
        parser.error('--bits must be 1..128')
    args.upper = args.upper if args.upper is not None else min(1 << (args.bits or 64), MAX_UPPER)
    if not 1 <= args.upper <= MAX_UPPER:
        parser.error('--upper must be 1..2^128-1')
    if args.threads < 1 or args.chunk_size < 1:
        parser.error('threads and chunk size must be positive')
    return args


def run(args):
    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=True)
    # OS releases the lock even after a crash; stale files are harmless.
    with (work / 'run.lock').open('a+b') as lock:
        if os.name == 'nt':
            import msvcrt
            lock.seek(0); lock.write(b'0'); lock.flush(); lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return run_locked(args, work)


def run_locked(args, work):
    kinds = ['negative', 'non_one'] if args.kind == 'both' else [args.kind]
    engine = args.engine.resolve()
    identity = {'format': 3, 'kinds': kinds,
                'chunk_size': args.chunk_size,
                'sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in [Path(__file__).resolve(), HERE / 'search.cpp', engine]}}
    manifest = work / 'identity.json'
    if manifest.exists():
        previous_identity = json.loads(manifest.read_text())
        legacy = dict(identity, format=2, upper_inclusive=previous_identity.get('upper_inclusive'))
        legacy['sha256'] = dict(identity['sha256'], **{
            'records.py': LEGACY_RECORDS_SHA256})
        legacy_previous_engine = dict(legacy, sha256=dict(legacy['sha256'],
            **{'search.exe': PREVIOUS_SEARCH_SHA256}))
        migrating = previous_identity in (legacy, legacy_previous_engine)
        previous_v3 = dict(identity, sha256=dict(identity['sha256'],
                           **{'records.py': PREVIOUS_FORMAT3_SHA256}))
        previous_v3_previous_engine = dict(previous_v3, sha256=dict(
            previous_v3['sha256'], **{'search.exe': PREVIOUS_SEARCH_SHA256}))
        previous_v3_baseline = dict(identity, sha256=dict(identity['sha256'],
            **{'records.py': PREVIOUS_FORMAT3_BASELINE_SHA256,
               'search.exe': PREVIOUS_SEARCH_SHA256}))
        previous_v3_match = previous_identity in (
            previous_v3, previous_v3_previous_engine, previous_v3_baseline)
        old_records = previous_identity == dict(
            identity, format=1, upper_inclusive=previous_identity.get('upper_inclusive'),
            sha256=FORMAT1_HASHES)
        if previous_identity != identity and not previous_v3_match and not migrating and not old_records:
            raise ValueError('code/configuration changed; use another work directory')
        state = json.loads((work / 'status.json').read_text())
        if old_records and state.get('job_root') == 'records-v3':
            # Recover a migration interrupted between publishing state and identity.
            state = json.loads((work / 'status.format1.json').read_text())
        if args.upper < state['upper_inclusive']:
            raise ValueError('upper bound cannot decrease; keep or increase --upper/--bits')
        if old_records:
            # Format 1 stores every update point but not every prime minimum. The
            # old covered prefix is still sufficient for finding later updates:
            # search only for witnesses above its largest recorded witness.
            for name, content in [('identity', previous_identity), ('status', state)]:
                backup = work / f'{name}.format1.json'
                if backup.exists() and json.loads(backup.read_text()) != content:
                    raise ValueError('legacy backup differs; refusing to overwrite')
                save(backup, content)
            state['job_root'] = 'records-v3'
            for kind, info in state['searches'].items():
                info['minima'] = [dict(row) for row in info['records']]
                info['minima_complete'] = False
                info.pop('active_job', None)
            print('Migrating format 1: preserving the covered prefix and update points.',
                  flush=True)
            publish(work, state)
            save(manifest, identity)
        elif previous_v3_match:
            save(manifest, identity)
        if not old_records:
            for info in state['searches'].values():
                info.setdefault('minima_complete', True)
        if migrating:
            # Preserve the old active range before changing the target bound.
            for kind, info in state['searches'].items():
                if info['covered_inclusive'] < state['upper_inclusive']:
                    info['active_job'] = {
                        'lower': info['covered_inclusive'] + 1,
                        'upper': next_upper(info['covered_inclusive'], state['upper_inclusive']),
                        'threshold': next(p for p in primes()
                                          if p not in {row['witness'] for row in info['minima']})}
            publish(work, state)
            save(manifest, identity)
        state['upper_inclusive'] = args.upper
        for info in state['searches'].values():
            info['complete'] = info['covered_inclusive'] == args.upper
        state['complete'] = all(info['complete'] for info in state['searches'].values())
        publish(work, state)
    else:
        covered = min(args.upper, INITIAL_UPPER)
        state = {'upper_inclusive': args.upper, 'complete': False, 'searches': {}}
        for kind in kinds:
            minima = reference_minima(covered, kind)
            state['searches'][kind] = {
                'covered_inclusive': covered, 'complete': covered == args.upper,
                'minima': minima, 'minima_complete': True,
                'records': record_rows(minima)}
        publish(work, state)
        save(manifest, identity)
    for kind in kinds:
        info = state['searches'][kind]
        while not info['complete']:
            found = {row['witness']: row['n'] for row in info['minima']}
            if info.get('minima_complete', True):
                threshold = next(p for p in primes() if p not in found)
            else:
                threshold = next(p for p in primes() if p > max(found, default=0))
            if threshold > 997:
                raise RuntimeError('engine threshold limit 997 reached; search is incomplete')
            lower = info['covered_inclusive'] + 1
            active = info.get('active_job')
            if active is None:
                active = {'lower': lower, 'upper': next_upper(info['covered_inclusive'], args.upper),
                          'threshold': threshold}
                info['active_job'] = active
                publish(work, state)
            if (active['lower'] != lower or active['threshold'] != threshold or
                    not lower <= active['upper'] <= args.upper or
                    active['upper'] - lower + 1 > MAX_INTERVAL):
                raise ValueError('active job parameters mismatch')
            upper = active['upper']
            job = work / state.get('job_root', '') / f'{kind}_t{threshold}_u{upper}'
            job.mkdir(parents=True, exist_ok=True)
            cmd = [str(engine), '--lower', str(lower),
                   '--upper-exclusive', str(upper + 1), '--threshold', str(threshold),
                   '--threads', str(args.threads), '--chunk-size', str(args.chunk_size),
                   '--work-dir', str(job)]
            if kind == 'non_one':
                cmd.append('--non-one')
            print(f'{kind}: {lower} <= n <= {upper}, witness >= {threshold}', flush=True)
            # Deleting the stop marker is an explicit request to resume this job.
            if (job / 'stop.request').exists():
                print(f'Remove {job / "stop.request"} to resume.', file=sys.stderr)
                return 130
            with (job / 'search.log').open('a', encoding='utf-8') as log:
                process = subprocess.Popen(cmd, stdout=log, stderr=subprocess.STDOUT)
                try:
                    code = process.wait()
                except KeyboardInterrupt:
                    (job / 'stop.request').touch()
                    process.wait()
                    return 130
            if code:
                raise RuntimeError(f'engine exited {code}; see {job / "search.log"}')
            minima = reduce_job(job, kind, threshold, upper, lower)
            for p, n in minima.items():
                if p in found:
                    if n < found[p]:
                        raise ValueError('candidate contradicts saved prime minimum')
                else:
                    if n <= info['covered_inclusive']:
                        raise ValueError('candidate contradicts completed prefix')
                    found[p] = n
            info['minima'] = [{'n': n, 'witness': p} for p, n in sorted(found.items())]
            info['records'] = record_rows(info['minima'])
            info['covered_inclusive'] = upper
            info['complete'] = upper == args.upper
            del info['active_job']
            publish(work, state)
    state['complete'] = all(info['complete'] for info in state['searches'].values())
    publish(work, state)
    return 0


if __name__ == '__main__':
    try:
        sys.exit(run(parse_args()))
    except (OSError, ValueError, RuntimeError) as error:
        print(f'error: {error}', file=sys.stderr)
        sys.exit(1)
