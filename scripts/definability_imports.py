"""Remove redundant imports from the Definability entry point, without removing modules."""
import argparse
from pathlib import Path
from lean_sources import import_graph, minimal_entry_imports

ROOT = Path(__file__).resolve().parent.parent
ENTRY = 'equational_theories.Definability'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    graph = import_graph(ROOT, ENTRY)
    selected = minimal_entry_imports(graph, ENTRY)
    # Independently verify that the proposed entry imports retain every local module.
    visited, todo = {ENTRY}, list(selected)
    while todo:
        name = todo.pop()
        if name in visited or name not in graph:
            continue
        visited.add(name)
        todo.extend(graph[name])
    if visited != set(graph):
        raise RuntimeError(f'Pruning would lose modules: {sorted(set(graph) - visited)}')
    path = ROOT / 'equational_theories/Definability.lean'
    # Preserve module documentation and non-import content; only redundant edges are removed.
    kept, seen = set(selected), set()
    lines = []
    for line in path.read_text().splitlines(keepends=True):
        if line.startswith('import '):
            name = line.strip().removeprefix('import ')
            if name not in kept or name in seen:
                continue
            seen.add(name)
        lines.append(line)
    if seen != kept:
        raise RuntimeError('Unsupported entry-point import syntax; no file changed')
    content = ''.join(lines)
    if args.check and content != path.read_text():
        raise SystemExit('Redundant entry imports; run scripts/definability_imports.py --write')
    if args.write and content != path.read_text():
        path.write_text(content)
    print(f'Entry imports: {len(graph[ENTRY])} -> {len(selected)}; '
          f'all {len(graph)} reachable local modules retained.')


if __name__ == '__main__':
    main()
