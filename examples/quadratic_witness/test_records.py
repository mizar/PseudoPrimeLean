"""Independent exhaustive comparison and restart/parameter regression tests."""
import csv
import json
import io
import os
from pathlib import Path
import subprocess
import sys
import time
from contextlib import contextmanager, redirect_stderr
from itertools import product
from uuid import uuid4
import unittest
from unittest.mock import patch

import records

ENGINE = records.HERE / ('search.exe' if os.name == 'nt' else 'search')


@contextmanager
def test_directory():
    # Avoid tempfile's mode=0700 ACL on sandboxed Windows. Keep ignored evidence.
    path = records.HERE / '_test' / uuid4().hex
    path.mkdir(parents=True)
    yield path


def jacobi(a, n):
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0


class RecordsTest(unittest.TestCase):
    def test_interval_cap_boundaries(self):
        cap = 1 << 64
        self.assertEqual(records.MAX_INTERVAL, cap)
        for covered, target, expected in [
                (10000, 200000, 160000),
                (cap // 15, 1 << 80, (cap // 15) * 16),
                (cap, 1 << 80, 2 * cap),
                (1 << 80, 1 << 81, (1 << 80) + cap),
                (records.MAX_UPPER - 10, records.MAX_UPPER, records.MAX_UPPER)]:
            with self.subTest(covered=covered):
                upper = records.next_upper(covered, target)
                self.assertEqual(upper, expected)
                self.assertLessEqual(upper - covered, cap)
                self.assertGreater(upper, covered)

    def test_capped_intervals_are_contiguous(self):
        with test_directory() as work, patch.object(records, 'INITIAL_UPPER', 3), \
                patch.object(records, 'MAX_INTERVAL', 32):
            args = records.parse_args(['--upper', '100', '--kind', 'non_one',
                                       '--threads', '2', '--chunk-size', '8',
                                       '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            intervals = []
            for path in work.glob('non_one_*/branch.json'):
                branch = json.loads(path.read_text())
                intervals.append((int(branch['lower_inclusive']),
                                  int(branch['upper_exclusive'])))
            end = 4
            for lower, upper in sorted(intervals):
                self.assertEqual(lower, end)
                self.assertLessEqual(upper - lower, 32)
                end = upper
            self.assertEqual(end, 101)
            state = json.loads((work/'status.json').read_text())
            self.assertEqual(state['searches']['non_one']['minima'],
                             records.reference_minima(100, 'non_one'))
            self.assertEqual(records.run(args), 0)

    def test_bounds(self):
        self.assertEqual(records.parse_args([]).upper, 2**64)
        self.assertEqual(records.parse_args(['--bits', '80']).upper, 2**80)
        self.assertEqual(records.parse_args(['--upper', '18446744073709551617']).upper, 2**64 + 1)
        self.assertEqual(records.parse_args(['--bits', '128']).upper, 2**128 - 1)
        self.assertEqual(records.parse_args(['--upper', str(2**128 - 1)]).upper, 2**128 - 1)
        for argv in [['--bits', '129'], ['--upper', str(2**128)],
                     ['--upper', str(2**256)], ['--upper', '-1']]:
            with self.assertRaises(SystemExit), redirect_stderr(io.StringIO()):
                records.parse_args(argv)

    def test_symbols(self):
        for n in [3, 15, 91, 399, 2**64 + 1, 2**80 - 1, 2**96+1, 2**127-1, 2**128-1,
                  5073529011861079155, 900328310767395396567151]:
            for kind in ['negative', 'non_one']:
                p = next(p for p in records.primes()
                         if jacobi(n, p) == -1 or (kind == 'non_one' and jacobi(n, p) == 0))
                self.assertEqual(records.witness(n, kind), p)
        self.assertEqual(records.witness(3, 'negative'), 5)
        self.assertEqual(records.witness(3, 'non_one'), 3)
        self.assertEqual(records.witness(15, 'negative'), 13)
        self.assertEqual(records.witness(5073529011861079155, 'negative'), 337)
        self.assertEqual(records.witness(900328310767395396567151, 'non_one'), 397)

    def test_full_workflow(self):
        with test_directory() as temp:
            work = Path(temp)
            args = records.parse_args(['--upper', '200000', '--threads', '2',
                                       '--chunk-size', '1000', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            self.assertTrue(json.loads((work / 'status.json').read_text())['complete'])
            for kind in ['negative', 'non_one']:
                with (work / f'{kind}_records.csv').open() as f:
                    actual = [{k: int(v) for k, v in row.items()} for row in csv.DictReader(f)]
                self.assertEqual(actual, records.reference(200000, kind))
                expected = {}
                for n in range(3, 200001, 2):
                    if records.isqrt(n)**2 != n:
                        p = next(p for p in records.primes()
                                 if jacobi(n, p) == -1 or
                                 (kind == 'non_one' and jacobi(n, p) == 0))
                        expected.setdefault(p, n)
                with (work / f'{kind}_prime_minima.csv').open() as f:
                    rows = list(csv.DictReader(f))
                found = {int(row['witness']): int(row['n']) for row in rows if row['n']}
                self.assertEqual(found, expected)
                self.assertEqual([int(row['witness']) for row in rows],
                                 [p for p in range(3, max(expected) + 1, 2)
                                  if all(p % d for d in range(3, records.isqrt(p) + 1, 2))])
            snapshot = (work / 'status.json').read_bytes()
            self.assertEqual(records.run(args), 0)
            self.assertEqual((work / 'status.json').read_bytes(), snapshot)
            args.chunk_size += 1
            with self.assertRaisesRegex(ValueError, 'changed'):
                records.run(args)

    def test_extend_completed_range_and_reject_shrink(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '10001', '--threads', '2',
                                       '--chunk-size', '8', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            saved = {p: p.read_bytes() for p in work.glob('*/odd/results-*.journal')}
            args.upper = 12000
            self.assertEqual(records.run(args), 0)
            for path, content in saved.items():
                self.assertEqual(path.read_bytes(), content)
            state = json.loads((work/'status.json').read_text())
            self.assertTrue(state['complete'])
            self.assertEqual(state['upper_inclusive'], 12000)
            for kind in ['negative', 'non_one']:
                self.assertEqual(state['searches'][kind]['minima'],
                                 records.reference_minima(12000, kind))
                branches = [json.loads(p.read_text()) for p in work.glob(f'{kind}_*/branch.json')]
                self.assertTrue(any(int(p['lower_inclusive']) == 10002 for p in branches))
            args.upper = 11000
            snapshot = (work/'status.json').read_bytes()
            with self.assertRaisesRegex(ValueError, 'cannot decrease'):
                records.run(args)
            self.assertEqual((work/'status.json').read_bytes(), snapshot)

    def test_extend_preserves_incomplete_job(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '20000', '--kind', 'negative',
                                       '--threads', '2', '--chunk-size', '1',
                                       '--work-dir', str(work)])
            real_popen = subprocess.Popen
            def partial(command, **kwargs):
                return real_popen(command + ['--chunk-end', '1'], **kwargs)
            with patch.object(records.subprocess, 'Popen', side_effect=partial):
                with self.assertRaisesRegex(ValueError, 'incomplete'):
                    records.run(args)
            state = json.loads((work/'status.json').read_text())
            active = state['searches']['negative']['active_job']
            self.assertEqual(active['upper'], 20000)
            old = {p: p.read_bytes() for p in work.glob('*/odd/results-*.journal')}
            identity_path = work/'identity.json'
            identity = json.loads(identity_path.read_text())
            identity['sha256']['records.py'] = records.PREVIOUS_FORMAT3_SHA256
            identity['sha256']['search.exe'] = records.PREVIOUS_SEARCH_SHA256
            records.save(identity_path, identity)
            args.upper = 21000
            self.assertEqual(records.run(args), 0)
            for path, content in old.items():
                self.assertTrue(path.read_bytes().startswith(content))
            state = json.loads((work/'status.json').read_text())
            self.assertEqual(state['searches']['negative']['minima'],
                             records.reference_minima(21000, 'negative'))
            self.assertNotIn('active_job', state['searches']['negative'])

    def test_migrate_previous_interval_capped_format(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '10000', '--kind', 'non_one',
                                       '--threads', '2', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            path = work/'identity.json'
            identity = json.loads(path.read_text())
            identity.update(format=2, upper_inclusive=10000)
            identity['sha256']['records.py'] = records.LEGACY_RECORDS_SHA256
            records.save(path, identity)
            args.upper = 11000
            self.assertEqual(records.run(args), 0)
            self.assertEqual(json.loads(path.read_text())['format'], 3)
            self.assertEqual(json.loads((work/'status.json').read_text())['searches']['non_one']['minima'],
                             records.reference_minima(11000, 'non_one'))

    def test_migrate_records_only_directory_and_extend(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '20000', '--threads', '2',
                                       '--chunk-size', '8', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            identity = json.loads((work/'identity.json').read_text())
            identity.update(format=1, upper_inclusive=20000, sha256=records.FORMAT1_HASHES)
            state = json.loads((work/'status.json').read_text())
            for info in state['searches'].values():
                info['records'] = records.record_rows(info['minima'])
                del info['minima']
            records.save(work/'identity.json', identity)
            records.save(work/'status.json', state)
            legacy = work/'negative_t17_u12000'
            legacy.mkdir()
            (legacy/'keep').write_bytes(b'old checkpoint')
            args.upper = 30000
            real_save = records.save
            def interrupt_manifest(path, value):
                if path == work/'identity.json':
                    raise OSError('simulated migration interruption')
                real_save(path, value)
            with patch.object(records, 'save', side_effect=interrupt_manifest):
                with self.assertRaisesRegex(OSError, 'migration interruption'):
                    records.run(args)
            self.assertEqual(records.run(args), 0)
            self.assertEqual(json.loads((work/'status.format1.json').read_text()), state)
            self.assertEqual(json.loads((work/'identity.format1.json').read_text()), identity)
            self.assertEqual((legacy/'keep').read_bytes(), b'old checkpoint')
            args.upper = 40000
            self.assertEqual(records.run(args), 0)
            result = json.loads((work/'status.json').read_text())
            self.assertTrue(result['complete'])
            for kind in ['negative', 'non_one']:
                info = result['searches'][kind]
                self.assertFalse(info['minima_complete'])
                self.assertEqual(info['records'],
                                 records.reference(40000, kind))
            self.assertTrue(any((work/'records-v3').glob('*/branch.json')))
            migrated_branches = [json.loads(p.read_text()) for p in
                                 (work/'records-v3').glob('*/branch.json')]
            self.assertTrue(all(int(p['lower_inclusive']) > 20000
                                for p in migrated_branches))
            self.assertIn(20001, {int(p['lower_inclusive'])
                                  for p in migrated_branches})

    def test_migrate_previous_format3_writer(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '10000', '--kind', 'non_one',
                                       '--threads', '2', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            path = work/'identity.json'
            identity = json.loads(path.read_text())
            identity['sha256']['records.py'] = records.PREVIOUS_FORMAT3_SHA256
            identity['sha256']['search.exe'] = records.PREVIOUS_SEARCH_SHA256
            records.save(path, identity)
            args.upper = 11000
            self.assertEqual(records.run(args), 0)
            self.assertEqual(json.loads((work/'status.json').read_text())['searches']['non_one']['minima'],
                             records.reference_minima(11000, 'non_one'))

    def test_migrate_initial_format3_writer(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '10000', '--kind', 'non_one',
                                       '--threads', '2', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            path = work/'identity.json'
            identity = json.loads(path.read_text())
            identity['sha256']['records.py'] = records.PREVIOUS_FORMAT3_BASELINE_SHA256
            identity['sha256']['search.exe'] = records.PREVIOUS_SEARCH_SHA256
            records.save(path, identity)
            args.upper = 11000
            self.assertEqual(records.run(args), 0)
            self.assertEqual(json.loads((work/'status.json').read_text())['searches']['non_one']['minima'],
                             records.reference_minima(11000, 'non_one'))

    def test_migrate_incomplete_previous_format(self):
        with test_directory() as work:
            args = records.parse_args(['--upper', '10000', '--kind', 'non_one',
                                       '--threads', '2', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            state = json.loads((work/'status.json').read_text())
            state.update(upper_inclusive=11000, complete=False)
            state['searches']['non_one']['complete'] = False
            records.save(work/'status.json', state)
            identity = json.loads((work/'identity.json').read_text())
            identity.update(format=2, upper_inclusive=11000)
            identity['sha256']['records.py'] = records.LEGACY_RECORDS_SHA256
            records.save(work/'identity.json', identity)
            args.upper = 12000
            self.assertEqual(records.run(args), 0)
            branches = [json.loads(p.read_text()) for p in work.glob('non_one_*/branch.json')]
            self.assertEqual(sorted((int(p['lower_inclusive']), int(p['upper_exclusive']))
                                    for p in branches), [(10001, 11001), (11001, 12001)])
            state = json.loads((work/'status.json').read_text())
            self.assertEqual(state['searches']['non_one']['minima'],
                             records.reference_minima(12000, 'non_one'))

    def test_prime_minimum_gaps_and_nonrecords(self):
        minima = [{'witness': 3, 'n': 5}, {'witness': 5, 'n': 3},
                  {'witness': 11, 'n': 101}, {'witness': 13, 'n': 51}]
        self.assertEqual(list(records.prime_minimum_rows(minima)), [
            {'witness': 3, 'n': 5}, {'witness': 5, 'n': 3},
            {'witness': 7, 'n': ''}, {'witness': 11, 'n': 101},
            {'witness': 13, 'n': 51}])
        self.assertEqual(records.record_rows(minima), [
            {'witness': 5, 'n': 3}, {'witness': 13, 'n': 51}])

    def test_lower_prime_can_first_appear_after_larger_prime(self):
        with test_directory() as work, patch.object(records, 'INITIAL_UPPER', 3):
            args = records.parse_args(['--upper', '1000', '--threads', '2',
                                       '--chunk-size', '32', '--work-dir', str(work)])
            self.assertEqual(records.run(args), 0)
            state = json.loads((work/'status.json').read_text())
            for kind in ['negative', 'non_one']:
                self.assertEqual(state['searches'][kind]['minima'],
                                 records.reference_minima(1000, kind))
            # Negative p=5 first appears at n=3; p=3 appears later at n=5.
            minima = {row['witness']: row['n'] for row in state['searches']['negative']['minima']}
            self.assertEqual((minima[3], minima[5]), (5, 3))

    def test_engine_low_threshold_and_resume(self):
        # Direct engine run covers initial zero witnesses and square exclusion.
        with test_directory() as temp:
            for kind in ['negative', 'non_one']:
                job = Path(temp) / kind
                cmd = [str(ENGINE), '--upper-exclusive', '3001', '--threshold', '3',
                       '--threads', '2', '--chunk-size', '100', '--checkpoint-seconds', '0',
                       '--work-dir', str(job)]
                if kind == 'non_one':
                    cmd.append('--non-one')
                partial = subprocess.run(cmd + ['--chunk-end', '1'], capture_output=True)
                self.assertEqual(partial.returncode, 0, partial.stderr)
                with self.assertRaisesRegex(ValueError, 'incomplete'):
                    records.reduce_job(job, kind, 3, 3000)
                subprocess.run(cmd, check=True, capture_output=True)
                minima = records.reduce_job(job, kind, 3, 3000)
                expected = {}
                for n in range(3, 3001, 2):
                    if records.isqrt(n)**2 != n:
                        p = records.witness(n, kind)
                        expected.setdefault(p, n)
                self.assertEqual(minima, expected)
                # Missing chunk data must fail, even with a completed bitmap.
                next((job / 'odd').glob('results-*.journal')).unlink()
                with self.assertRaisesRegex(ValueError, 'missing result journal'):
                    records.reduce_job(job, kind, 3, 3000)

    def test_engine_direct_high_interval(self):
        lower = (1 << 64) + 101
        upper = lower + 5000
        with test_directory() as temp:
            for kind in ['negative', 'non_one']:
                job = Path(temp) / kind
                cmd = [str(ENGINE), '--lower', str(lower),
                       '--upper-exclusive', str(upper + 1), '--threshold', '3',
                       '--threads', '2', '--chunk-size', '1000',
                       '--checkpoint-seconds', '0', '--work-dir', str(job)]
                if kind == 'non_one':
                    cmd.append('--non-one')
                subprocess.run(cmd, check=True, capture_output=True)
                params = json.loads((job / 'branch.json').read_text())
                self.assertEqual(int(params['lower_inclusive']), lower)
                self.assertTrue((job / 'odd' / 'direct.range').exists())
                actual = records.reduce_job(job, kind, 3, upper, lower)
                expected = {}
                for n in range(lower, upper + 1, 2):
                    if records.isqrt(n) ** 2 != n:
                        expected.setdefault(records.witness(n, kind), n)
                self.assertEqual(actual, expected)

    def test_journal_recovery_and_bounded_files(self):
        with test_directory() as job:
            cmd = [str(ENGINE), '--upper-exclusive', '10001', '--threshold', '3',
                   '--threads', '2', '--chunk-size', '8', '--checkpoint-seconds', '0',
                   '--work-dir', str(job)]
            subprocess.run(cmd, check=True, capture_output=True)
            expected = records.reduce_job(job, 'negative', 3, 10000)
            journals = sorted((job/'odd').glob('results-*.journal'))
            self.assertLessEqual(len(journals), records.RESULT_SHARDS)
            self.assertFalse(list((job/'odd').glob('chunk-*')))
            snapshot = {p.name: p.read_bytes() for p in journals}
            h = records.struct.unpack('<8s10Q', (job/'odd/done.bitmap').read_bytes()[:88])
            self.assertGreater(h[2], 100)
            # A killed writer can leave a partial header or partial payload.
            for suffix in [b'QWJN', records.struct.pack('<8s3Q', b'QWJNL001', 0, 20, 0) + b'1,3']:
                with journals[0].open('ab') as f:
                    f.write(suffix)
                with self.assertRaisesRegex(ValueError, 'incomplete result journal'):
                    records.reduce_job(job, 'negative', 3, 10000)
                (job/'odd/done.bitmap').unlink()
                resumed = cmd.copy()
                resumed[resumed.index('--threads') + 1] = '3'
                subprocess.run(resumed, check=True, capture_output=True)
                self.assertEqual(snapshot, {p.name: p.read_bytes() for p in journals})
                self.assertEqual(records.reduce_job(job, 'negative', 3, 10000), expected)
            # A complete but corrupt frame must never be silently discarded.
            original = journals[0].read_bytes()
            damaged = bytearray(original)
            damaged[24] ^= 1
            journals[0].write_bytes(damaged)
            with self.assertRaisesRegex(ValueError, 'checksum'):
                records.reduce_job(job, 'negative', 3, 10000)
            result = subprocess.run(cmd, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'checksum', result.stderr)
            self.assertEqual(journals[0].read_bytes(), damaged)
            journals[0].write_bytes(original + original[:32 + records.struct.unpack('<Q', original[16:24])[0]])
            with self.assertRaisesRegex(ValueError, 'duplicate'):
                records.reduce_job(job, 'negative', 3, 10000)
            result = subprocess.run(cmd, capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'duplicate', result.stderr)

    def test_killed_process_and_stop_marker_resume(self):
        with test_directory() as job:
            cmd = [str(ENGINE), '--upper-exclusive', '50001', '--threshold', '3',
                   '--threads', '2', '--chunk-size', '8', '--checkpoint-seconds', '0',
                   '--work-dir', str(job)]
            (job/'stop.request').touch()
            stopped = subprocess.run(cmd, capture_output=True)
            self.assertEqual(stopped.returncode, 130, stopped.stderr)
            with self.assertRaisesRegex(ValueError, 'incomplete'):
                records.reduce_job(job, 'negative', 3, 50000)
            (job/'stop.request').unlink()
            with (job/'killed.log').open('wb') as log:
                process = subprocess.Popen(cmd, stdout=log, stderr=log)
                try:
                    deadline = time.monotonic() + 15
                    while not any(p.stat().st_size >= 32 for p in (job/'odd').glob('results-*.journal')):
                        if process.poll() is not None or time.monotonic() > deadline:
                            self.fail('engine did not produce a journal before termination')
                        time.sleep(0.005)
                    process.kill()
                    process.wait(timeout=15)
                finally:
                    if process.poll() is None:
                        process.kill()
                        process.wait(timeout=15)
            cmd[cmd.index('--threads') + 1] = '3'
            subprocess.run(cmd, check=True, capture_output=True)
            actual = records.reduce_job(job, 'negative', 3, 50000)
            expected = {}
            for n in range(3, 50001, 2):
                if records.isqrt(n)**2 != n:
                    expected.setdefault(records.witness(n, 'negative'), n)
            self.assertEqual(actual, expected)
            h = records.struct.unpack('<8s10Q', (job/'odd/done.bitmap').read_bytes()[:88])
            counts = sum(row['count'] for row in records.journal_rows(job/'odd', h[2]))
            self.assertEqual(counts, sum(records.isqrt(n)**2 != n for n in range(3, 50001, 2)))
            self.assertLessEqual(len(list((job/'odd').glob('results-*.journal'))), records.RESULT_SHARDS)

    def test_engine_full_128_bit_windows(self):
        maximum = 2**128 - 1
        square = (2**64 - 1)**2
        windows = [(2**64-65, 2**64+65), (2**96-65, 2**96+65),
                   (2**127-65, 2**127+65), (square-65, square+65),
                   (maximum-256, maximum)]
        known = 900328310767395396567151
        windows.append((known-65, known+65))
        for lower, upper in windows:
            settings = [(3, 3), (17, 7)]
            if lower <= known <= upper:
                settings.append((131, 17))
            for kind, (threshold, wheel_limit) in product(['negative', 'non_one'], settings):
                with self.subTest(lower=lower, kind=kind, threshold=threshold), test_directory() as work:
                    bounds = (['--bits', '128'] if upper == maximum and threshold == 3
                              else ['--upper-exclusive', str(upper+1)])
                    cmd = [str(ENGINE)] + bounds + [
                           '--lower', str(lower), '--threshold', str(threshold),
                           '--wheel-limit', str(wheel_limit),
                           '--threads', '2', '--chunk-size', '32', '--checkpoint-seconds', '0',
                           '--work-dir', str(work)]
                    if kind == 'non_one':
                        cmd.append('--non-one')
                    if upper == maximum and threshold == 3:
                        subprocess.run(cmd + ['--chunk-end', '1'], check=True, capture_output=True)
                    subprocess.run(cmd, check=True, capture_output=True)
                    snapshot = {p.name: p.read_bytes() for p in (work/'odd').glob('results-*.journal')}
                    subprocess.run(cmd, check=True, capture_output=True)
                    self.assertEqual(snapshot, {p.name: p.read_bytes() for p in (work/'odd').glob('results-*.journal')})
                    expected, counts = {}, {}
                    for n in range(lower | 1, upper+1, 2):
                        if records.isqrt(n)**2 == n:
                            continue
                        p = records.witness(n, kind)
                        if p < threshold:
                            continue
                        expected.setdefault(p, n)
                        counts[p] = counts.get(p, 0) + 1
                    actual, actual_counts = {}, {}
                    h = records.struct.unpack('<8s10Q', (work/'odd/done.bitmap').read_bytes()[:88])
                    for row in records.journal_rows(work/'odd', h[2]):
                        q, n, count = row['witness'], row['n'], row['count']
                        actual[q] = min(actual.get(q, n), n)
                        actual_counts[q] = actual_counts.get(q, 0) + count
                    self.assertEqual(actual, expected)
                    self.assertEqual(actual_counts, counts)
                    h = records.struct.unpack('<8s10Q', (work/'odd/done.bitmap').read_bytes()[:88])
                    self.assertEqual((h[-2] << 64) | h[-1], upper)
                    self.assertEqual(json.loads((work/'branch.json').read_text())['upper_exclusive'], str(upper+1))

    def test_engine_rejects_overflowing_bounds(self):
        for upper in [str(2**128+1), str(2**256), '', '-1', '12x']:
            result = subprocess.run([str(ENGINE), '--upper-exclusive', upper], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'error:', result.stderr)


if __name__ == '__main__':
    unittest.main()
