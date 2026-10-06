#!/usr/bin/env python3
"""Bounded searches of the surviving order-12 rows, using Lean subclass exclusions.

These searches are research only: UNSAT excludes the specified row shape;
UNKNOWN is a timeout, not negative evidence. Saved SAT tables are checked
independently against E667. This is not an exhaustive order-12 refutation.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import subprocess
import time

from spectrum_667_incremental import clauses
from spectrum_generate import load_equations, satisfies

ROWS = [(1, 1, 4, 6), (1, 3, 3, 5), (1, 3, 4, 4),
        (1, 3, 8), (1, 4, 7), (1, 5, 6), (1, 11)]


def work(args, lengths):
    n, r = 12, range(12)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    cs = clauses(n, "one-idempotent")
    row, start = [], 0
    for k in lengths:
        row.extend(list(range(start + 1, start + k)) + [start])
        start += k
    cs.extend([[p(0, y, z)] for y, z in enumerate(row)])
    cnf = (f"p cnf {2*n**3} {len(cs)}\n" +
           "".join(" ".join(map(str, c)) + " 0\n" for c in cs)).encode()
    base = args.output / ("-".join(map(str, lengths)))
    base.with_suffix(".cnf").write_bytes(cnf)
    command = [args.solver, "--quiet", "-t", str(args.seconds),
               str(base.with_suffix(".cnf"))]
    if args.lrat:
        command[1:1] = ["--shrink=0", "--lrat", "--no-binary"]
        command.append(str(base.with_suffix(".lrat")))
    start_time = time.monotonic()
    result = subprocess.run(command, capture_output=True, text=True)
    record = dict(law=667, order=n, mode="one-idempotent", cycles=lengths,
                  restriction="chosen idempotent row has this cycle shape",
                  extra_constraints="Lean exclusions: no globally idempotent or right-unital order-12 model",
                  status={10: "SAT", 20: "UNSAT"}.get(result.returncode, "UNKNOWN"),
                  cpu_time_limit=args.seconds, wall_seconds=round(time.monotonic()-start_time, 3),
                  cnf_sha256=sha256(cnf).hexdigest(), clauses=len(cs),
                  proof_status="external search; no Lean replay")
    if result.returncode == 10:
        values = {int(v) for line in result.stdout.splitlines() if line.startswith("v ")
                  for v in line.split()[1:]}
        table = [next(z for z in r if p(x, y, z) in values) for x, y in product(r, repeat=2)]
        assert satisfies(*load_equations()[666], table, n)
        record["table"] = table
    base.with_suffix(".out").write_text(result.stdout + result.stderr)
    base.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cycles", help="one comma-separated row shape; default all seven")
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--lrat", action="store_true")
    parser.add_argument("--output", type=Path, default=Path(".cache/e667-subclass-rows"))
    args = parser.parse_args()
    if args.seconds < 1 or args.workers < 1:
        parser.error("seconds and workers must be positive")
    rows = [tuple(map(int, args.cycles.split(",")))] if args.cycles else ROWS
    if any(row not in ROWS for row in rows):
        parser.error("choose one of the seven archived surviving row shapes")
    args.output.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        records = list(pool.map(lambda row: work(args, row), rows))
    (args.output / "results.json").write_text(json.dumps(records, indent=2) + "\n")


if __name__ == "__main__":
    main()
