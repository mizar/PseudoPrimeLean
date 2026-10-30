#!/usr/bin/env python3
"""Render first-level project module dependencies; exclude hidden/archive trees.

Edges describe imports, not semantic ownership of declarations. Run from any cwd.
"""
import argparse
from collections import Counter, defaultdict
from pathlib import Path
import re

from check_namespace_layout import mask

# Display policy only: imports against this direction remain in the source.
# Unknown groups must be reviewed rather than silently omitted.
LAYERS = {
    'PseudoPrime': 0,
    'PseudoPrime.Tests': 1,
    'PseudoPrime.Tools': 2,
    'PseudoPrime.PrimeTestBounds': 3,
    'PseudoPrime.PseudoSquare': 4,
    'PseudoPrime.LLS': 5,
    'PseudoPrime.PrimeTest': 6,
    'PseudoPrime.AnalyticNumberTheory': 7,
    'PseudoPrime.NumberTheory': 8,
    'PseudoPrime.Analysis': 9,
    'PseudoPrime.Combinatorics': 9,
    'PseudoPrime.Data': 10,
}

def collect(root):
    files = []
    # Prune before traversal: never descend into dependency caches or archives.
    def visit(directory):
        for path in sorted(directory.iterdir()):
            if path.name.startswith('.') or path.name == 'archive':
                continue
            if path.is_symlink():
                continue
            if path.is_dir():
                visit(path)
            elif path.suffix == '.lean':
                files.append(path)
    visit(root)
    modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in files}
    groups = Counter()
    edges = defaultdict(list)
    external = Counter()
    for module, path in sorted(modules.items()):
        source = '.'.join(module.split('.')[:2])
        groups[source] += 1
        text = mask(path.read_text(encoding='utf-8-sig'))
        for match in re.finditer(r'^\s*(?:(?:public|private)\s+)?import\s+([^\n]+)',
                                 text, re.M):
            for target in match[1].split():
                if target not in modules:
                    external[target.split('.')[0]] += 1
                    continue
                destination = '.'.join(target.split('.')[:2])
                if source != destination:
                    edges[source, destination].append(
                        (path.relative_to(root).as_posix(), target))
    return groups, edges, external


def components(nodes, edges):
    reach = {n: {n} for n in nodes}
    for a, b in edges:
        reach[a].add(b)
    for k in nodes:
        for a in nodes:
            if k in reach[a]:
                reach[a].update(reach[k])
    remaining = set(nodes)
    result = []
    for a in sorted(nodes):
        if a not in remaining:
            continue
        group = sorted(b for b in nodes if b in reach[a] and a in reach[b])
        remaining.difference_update(group)
        if len(group) > 1:
            result.append(group)
    return result


def render(root):
    groups, edges, external = collect(root)
    unknown = set(groups) - LAYERS.keys()
    if unknown:
        raise ValueError(f'Review display layers for new groups: {sorted(unknown)}')
    shown = {(a, b): items for (a, b), items in edges.items() if LAYERS[a] < LAYERS[b]}
    omitted = {edge: items for edge, items in edges.items() if edge not in shown}
    assert not components(sorted(groups), shown)
    names = {n: n.removeprefix('PseudoPrime.') for n in groups}
    lines = [f'対象はチェックアウト内のLeanソース {sum(groups.values())} ファイル。'
             '隠しディレクトリ・ `archive` ・シンボリックリンク以下は走査しない。'
             '未追跡ファイルも含む。Mathlibなどの外部依存と同一グループ内の辺は図から除く。',
             '', '```mermaid', 'flowchart TD']
    ids = {n: f'N{i}' for i, n in enumerate(sorted(groups))}
    for n in sorted(groups):
        lines.append(f'    {ids[n]}["{names[n]} ({groups[n]})"]')
    for a, b in sorted(shown):
        lines.append(f'    {ids[a]} --> {ids[b]}')
    lines += ['```', '', 'ノードの括弧内はファイル数。名前は `PseudoPrime.` を省略している。'
              f'異なるグループ間の直接依存 {len(edges)} 方向のうち、配置方針に沿う '
              f'{len(shown)} 方向を表示する。図に表示しない '
              f'{len(omitted)} 方向は下表にすべて示す。'
              '表示する辺はすべて実際のimportに基づく。'
              '図から除いた依存がソース上で解消されたことを意味しない。']
    if omitted:
        lines += ['', '| 依存元 | 依存先 | import数 |', '|---|---|---|']
        for (a, b), items in sorted(omitted.items()):
            lines.append(f'| `{names[a]}` | `{names[b]}` | {len(items)} |')
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='Refresh the marked documentation block')
    parser.add_argument('--check', action='store_true', help='Fail if the documentation is stale')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    output = render(root)
    if not (args.write or args.check):
        print(output, end='')
        return 0
    path = root / 'doc' / 'NamespaceLayout.md'
    text = path.read_text(encoding='utf-8')
    start, end = '<!-- namespace-dependencies:start -->', '<!-- namespace-dependencies:end -->'
    before, rest = text.split(start, 1)
    old, after = rest.split(end, 1)
    if args.check:
        return int(old != '\n' + output)
    path.write_text(before + start + '\n' + output + end + after, encoding='utf-8', newline='\n')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
