"""Read repository-local Lean import graphs without reading large proof bodies.

Imports must precede declarations. Only the header is read, respecting nested
block comments and line comments. This is an import-coverage check, not a proof
checker: reachable modules still need to be built with Lean.
"""
from pathlib import Path


def imports(path):
    depth = 0
    with path.open() as stream:
        for line in stream:
            code, i = [], 0
            while i < len(line):
                if line.startswith('/-', i):
                    if not depth:
                        code.append(' ')
                    depth += 1
                    i += 2
                elif depth and line.startswith('-/', i):
                    depth -= 1
                    i += 2
                elif depth:
                    i += 1
                elif line.startswith('--', i):
                    break
                else:
                    code.append(line[i])
                    i += 1
            words = ''.join(code).split()
            if not words or words in [['prelude'], ['module']]:
                continue
            if words[0] in ('public', 'private'):
                words = words[1:]
            if not words or words[0] != 'import':
                break
            yield from words[1:]


def import_graph(root, entry='equational_theories.Definability'):
    """Map each reachable local module to its direct imports (including external)."""
    graph, todo = {}, [entry]
    while todo:
        name = todo.pop()
        if name in graph:
            continue
        parts = name.split('.')
        # These repository-owned libraries have a separate Lake source directory.
        native = parts[0] in {'DefSearch', 'DefOrbit'}
        directory = root / 'defsearch' if native else root
        path = directory / Path(*parts).with_suffix('.lean')
        if not path.exists():
            if native or name.startswith('equational_theories.') or name == entry:
                raise FileNotFoundError(f'Missing local Lean import: {name}')
            continue  # dependencies such as Mathlib have their own build targets
        graph[name] = tuple(imports(path))
        todo.extend(graph[name])
    return graph


def minimal_entry_imports(graph, entry):
    """Remove entry imports already required by other reachable local modules.

    Lean import graphs are acyclic. A directly imported module with another
    incoming edge therefore remains reachable after these redundant edges are
    removed. Preserve the order of the retained imports.
    """
    indirect = {child for name, children in graph.items() if name != entry for child in children}
    return list(dict.fromkeys(name for name in graph[entry] if name not in indirect))
