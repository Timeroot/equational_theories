#!/usr/bin/env python3
"""Search idempotent E667 with a prescribed automorphism, via cubic E229.

The SAT variables are orbits of table entries under simultaneous relabelling.
These are restricted searches: an exhausted orbit template is not an order
exclusion. Positive tables are checked against both original identities.
"""
import argparse
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_667_idempotent_search import checked_table


def encode(lengths):
    n = sum(lengths)
    permutation = []
    for length in lengths:
        offset = len(permutation)
        permutation.extend(offset + (j+1) % length for j in range(length))
    atoms = {}
    top = 0
    for triple in product(range(n), repeat=3):
        if triple in atoms:
            continue
        top += 1
        t = triple
        while t not in atoms:
            atoms[t] = top
            t = tuple(permutation[x] for x in t)
    reps, seen = [], set()
    for pair in product(range(n), repeat=2):
        if pair in seen:
            continue
        reps.append(pair)
        t = pair
        while t not in seen:
            seen.add(t)
            t = tuple(permutation[x] for x in t)
    clauses = set()

    def add(literals):
        literals = frozenset(literals)
        if any(-v in literals for v in literals):
            return
        clauses.add(tuple(sorted(literals)))

    def p(x, y, z):
        return atoms[x, y, z]

    for x, y in reps:
        for values in ([p(x, y, z) for z in range(n)],
                       [p(x, z, y) for z in range(n)],
                       [p(z, x, y) for z in range(n)]):
            add(values)
            for a, b in combinations(values, 2):
                add([-a, -b])
        for a, b in product(range(n), repeat=2):
            av, bv, cv = p(x, y, a), p(x, a, b), p(b, x, y)
            add([-av, -bv, cv])
            add([-av, bv, -cv])
            add([av, -bv, -cv])
        for z in range(n):
            if y != z:
                add([-p(x, y, z), -p(x, z, y)])
    for x in range(n):
        add([p(x, x, x)])
    return top, sorted(clauses), atoms, permutation


def run(lengths, seconds, workdir, fixed_affine=0):
    n = sum(lengths)
    stem = workdir / (str(n) + "-" + "-".join(map(str, lengths)))
    top, clauses, atoms, permutation = encode(lengths)
    if fixed_affine:
        from spectrum_63_bennett import prime
        assert lengths[:fixed_affine] == [1]*fixed_affine
        small = prime(fixed_affine) if fixed_affine > 1 else [[0]]
        checked_table(small)
        clauses.extend([[atoms[x,y,small[x][y]]]
                        for x in range(fixed_affine) for y in range(fixed_affine)])
    path = stem.with_suffix(".cnf")
    with path.open("w") as out:
        out.write(f"p cnf {top} {len(clauses)}\n")
        for c in clauses:
            out.write(" ".join(map(str, c)) + " 0\n")
    record = dict(order=n, automorphism_cycles=lengths, variables=top,
                  clauses=len(clauses), restriction="idempotent E229 with prescribed automorphism",
                  input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  limit_seconds=seconds)
    if fixed_affine:
        record['fixed_affine_submodel'] = fixed_affine
    del clauses
    command = ["cadical", "--quiet", "-t", str(seconds), str(path)]
    record["command"] = command
    start = time.monotonic()
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=seconds+10)
        output = result.stdout + result.stderr
        record["exit_code"] = result.returncode
        record["status"] = {10: "VERIFIED_MODEL", 20: "UNSAT_RESTRICTED_NO_LEAN_PROOF",
                            0: "TIME_LIMIT"}.get(result.returncode, "SOLVER_ERROR")
        if result.returncode == 10:
            values = {int(v) for line in output.splitlines() if line.startswith("v ")
                      for v in line[2:].split() if int(v) > 0}
            table = [[next(z for z in range(n) if atoms[x,y,z] in values)
                      for y in range(n)] for x in range(n)]
            record.update(e229_table=table, e63_table=checked_table(table))
            assert all(table[permutation[x]][permutation[y]] == permutation[table[x][y]]
                       for x in range(n) for y in range(n))
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or b"").decode(errors="replace")
        record["status"] = "WALL_TIME_LIMIT"
    record["wall_seconds"] = round(time.monotonic()-start, 3)
    stem.with_suffix(".log").write_text(output)
    stem.with_suffix(".json").write_text(json.dumps(record, indent=2)+"\n")
    print(n, lengths, record["status"], record["wall_seconds"], flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cycles", type=int, nargs="+")
    parser.add_argument("--seconds", type=int, default=90)
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--fixed-affine", type=int, default=0,
                        help="Prescribe the affine E229 table on the first p fixed points")
    args = parser.parse_args()
    assert args.seconds > 0 and min(args.cycles) > 0
    args.workdir.mkdir(parents=True, exist_ok=True)
    run(args.cycles, args.seconds, args.workdir, args.fixed_affine)


if __name__ == "__main__":
    main()
