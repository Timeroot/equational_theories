#!/usr/bin/env python3
"""Export the exploratory recovery encoding, preserving submitted clause order.

Usage: python3 scripts/definability_weak_central_export.py OUTPUT CASE [search flags]
The export and external UNSAT reports are not Lean certificates.
"""

import gzip
import hashlib
import json
import sys
from pathlib import Path

import pysat.solvers


def main():
    output = Path(sys.argv[1])
    arguments = sys.argv[2:]
    script = Path(__file__).with_name("definability_weak_central_recovery_search.py")
    real_solver = pysat.solvers.Solver
    count = 0
    phases = []
    header_size = 128
    with output.open("w+") as stream:
        stream.write("c" + " " * (header_size - 2) + "\n")

        class RecordingSolver:
            def __init__(self, *args, **kwargs):
                self.solver = real_solver(*args, **kwargs)

            def add_clause(self, clause, *args, **kwargs):
                nonlocal count
                stream.write(" ".join(map(str, clause)) + " 0\n")
                count += 1
                return self.solver.add_clause(clause, *args, **kwargs)

            def set_phases(self, literals):
                phases.extend(literals)
                return self.solver.set_phases(literals)

            def __getattr__(self, name):
                return getattr(self.solver, name)

        original_argv = sys.argv
        namespace = {"__file__": str(script), "__name__": "__main__"}
        pysat.solvers.Solver = RecordingSolver
        sys.argv = [str(script), *arguments, "--encode-only"]
        try:
            try:
                exec(compile(script.read_text(), str(script), "exec"), namespace)
            except SystemExit as exc:
                assert exc.code in (None, 0), exc.code
        finally:
            pysat.solvers.Solver = real_solver
            sys.argv = original_argv
        assert namespace["count"] == count
        pool = namespace["pool"]
        header = f"p cnf {pool.top} {count}"
        assert len(header) < header_size
        stream.seek(0)
        stream.write(header.ljust(header_size - 1) + "\n")

    # Validate the serialized formula without relying on the solver's parser.
    maximum = lines = 0
    digest = hashlib.sha256()
    with output.open("rb") as stream:
        for line in stream:
            digest.update(line)
            if line.startswith(b"p"):
                continue
            literals = list(map(int, line.split()))
            assert literals and literals[-1] == 0 and 0 not in literals[:-1]
            maximum = max(maximum, *(abs(x) for x in literals))
            lines += 1
    assert lines == count and maximum <= pool.top
    metadata = {
        "arguments": arguments,
        "variables": pool.top,
        "clauses": count,
        "sha256": digest.hexdigest(),
        "source_hashes": {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [
                script,
                script.with_name("definability_weak_central_constraints.py"),
                script.with_name("definability_weak_central_check.py"),
                script.with_name("1485_structure_check.py"),
                script.parent.parent / "data/definability_weak_central_recovery_search.json",
            ]
        },
        "phases": phases,
        "named_variables": pool.id2obj,
        "status": "exported exploratory encoding; no Lean certificate",
    }
    with gzip.open(str(output) + ".metadata.json.gz", "wt") as stream:
        json.dump(metadata, stream)
        stream.write("\n")
    print(f"EXPORTED {output}: {pool.top} variables, {count} clauses", flush=True)


if __name__ == "__main__":
    main()
