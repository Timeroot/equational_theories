#!/usr/bin/env python3
"""Bounded searches for idempotent E667 (= idempotent E63) seeds.

Search the left-division parastrophe E229, whose shorter cubic identity is
cheaper to encode. Every positive table is independently checked after
conversion back to E63 and E667. Exhaustion is external evidence only;
timeouts are not exclusions. No proof traces or Lean files are generated.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_63_atp import failure_status, mace_table, problem, validate
from spectrum_63_ten_certificate import clauses

ROOT = Path(__file__).resolve().parent.parent


def checked_table(table):
    n = len(table)
    validate(table, n, 229)
    assert all(table[x][x] == x for x in range(n))
    converted = [[table[x].index(y) for y in range(n)] for x in range(n)]
    validate(converted, n, 63)
    assert all(converted[x][x] == x for x in range(n))
    assert all(converted[y][converted[x][converted[converted[x][x]][y]]] == x
               for x in range(n) for y in range(n))
    return converted


def run(args, n, solver):
    lengths = getattr(args, "row_cycles", None)
    suffix = "-" + "-".join(map(str, lengths)) if lengths else ""
    stem = args.workdir / f"{n}-{solver}{suffix}"
    record = dict(order=n, solver=solver, encoding="idempotent E229", seconds=args.seconds)
    no_short_cycles = getattr(args, "no_three_four", False)
    no_three = no_short_cycles or getattr(args, "no_three", False)
    if no_three:
        record["additional_restriction"] = (
            "No 3- or 4-cycles in any left translation" if no_short_cycles
            else "No 3-cycles in any left translation")
        record["restriction_warning"] = "Requires separate row-case exclusions to infer a full exclusion"
    if lengths:
        from spectrum_667_idempotent_fifteen import row
        assert sum(lengths) == n - 1 and min(lengths) >= 3
        first_row = row(lengths)
        record["first_row_cycles"] = [1] + lengths
    if solver == "cadical":
        cs = clauses(n)
        cs.extend([[1 + (x * n + x) * n + x] for x in range(n)])
        if lengths:
            cs.extend([[1 + y*n + z] for y, z in enumerate(first_row)])
        if no_three:
            p = lambda x, y, z: 1 + (x*n+y)*n+z
            for x in range(n):
                for y in range(n):
                    if x == y:
                        continue
                    for a in range(n):
                        # R_x = L_x^(-2): L_x(y) = R_x(y) iff L_x^3(y) = y.
                        cs.append([-p(x, y, a), -p(y, x, a)])
                        if not no_short_cycles:
                            continue
                        for b in range(n):
                            # L_x^2(y) = R_x(y) iff L_x^4(y) = y.
                            cs.append([-p(x, y, a), -p(x, a, b), -p(y, x, b)])
        path = stem.with_suffix(".cnf")
        with path.open("w") as out:
            out.write(f"p cnf {n**3} {len(cs)}\n")
            for c in cs:
                out.write(" ".join(map(str, c)) + " 0\n")
        record.update(variables=n**3, clauses=len(cs), symmetry="first-row chain labelling")
        del cs
        command = [args.cadical, "--quiet", "-t", str(args.seconds), str(path)]
    else:
        source = problem(n, 229, "mace4", "idempotent", cancellation=True,
                         translation_hints=True, all_translations=True,
                         first_row_cycles=[1] + lengths if lengths else None)
        if no_three:
            source = source.replace("end_of_list.",
                "x = y | mul(x,y) != mul(y,x).\n" +
                ("x = y | mul(x,mul(x,y)) != mul(y,x).\n" if no_short_cycles else "") +
                "end_of_list.")
        path = stem.with_suffix(".in")
        path.write_text(source)
        command = [str(args.mace4), "-n", str(n), "-N", str(n), "-t",
                   str(args.seconds), "-b", "2048", "-f", str(path)]
        record["symmetry"] = "Mace4 least-number heuristic"
    record.update(command=command, input_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    started = time.monotonic()
    try:
        result = subprocess.run(command, capture_output=True, text=True,
                                timeout=args.seconds + 10)
        output = result.stdout + result.stderr
        record["exit_code"] = result.returncode
        if solver == "cadical" and result.returncode == 10:
            values = {int(v) for line in output.splitlines() if line.startswith("v ")
                      for v in line[2:].split() if int(v) > 0}
            table = [[next(z for z in range(n) if 1 + (x*n+y)*n+z in values)
                      for y in range(n)] for x in range(n)]
            record.update(status="VERIFIED_MODEL", e63_table=checked_table(table),
                          e229_table=table)
        elif solver == "mace4" and "end of model" in output:
            table = mace_table(output, n)
            record.update(status="VERIFIED_MODEL", e63_table=checked_table(table),
                          e229_table=table)
        elif solver == "cadical" and result.returncode == 20:
            record["status"] = "SOLVER_EXHAUSTED_NOT_A_LEAN_EXCLUSION"
        elif solver == "cadical" and ("s UNKNOWN" in output or result.returncode == 0):
            record["status"] = "TIME_LIMIT"
        else:
            record["status"] = failure_status(output)
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or b"").decode(errors="replace")
        record["status"] = "WALL_TIME_LIMIT"
    record["wall_seconds"] = round(time.monotonic() - started, 3)
    stem.with_suffix(".log").write_text(output)
    stem.with_suffix(".json").write_text(json.dumps(record, indent=2) + "\n")
    print(n, solver, record["status"], record["wall_seconds"], flush=True)
    return record


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--sat-orders", type=int, nargs="*", default=[13, 16, 17, 20, 22, 24])
    p.add_argument("--mace-orders", type=int, nargs="*", default=[13, 16, 20, 22, 24, 38])
    p.add_argument("--seconds", type=int, default=240)
    p.add_argument("--workers", type=int, default=6)
    p.add_argument("--row-cycles", type=int, nargs="+",
                   help="Cycle lengths after the unique fixed point in the first E229 row")
    p.add_argument("--no-three-four", action="store_true",
                   help="Restricted search: forbid 3- and 4-cycles in all left translations")
    p.add_argument("--no-three", action="store_true",
                   help="Restricted search: forbid 3-cycles in all left translations")
    p.add_argument("--cadical", default="cadical")
    p.add_argument("--mace4", type=Path,
                   default=ROOT / ".cache/e667-subclasses/LADR-2009-11A/bin/mace4")
    p.add_argument("--workdir", type=Path, required=True)
    args = p.parse_args()
    assert args.seconds > 0 and args.workers > 0
    assert all(n > 0 for n in args.sat_orders + args.mace_orders)
    args.workdir.mkdir(parents=True, exist_ok=True)
    jobs = [(n, "cadical") for n in args.sat_orders] + [(n, "mace4") for n in args.mace_orders]
    report = {"law": 667, "restriction": "idempotent", "attempts": []}
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run, args, *job) for job in jobs]
        for future in as_completed(futures):
            report["attempts"].append(future.result())
            (args.workdir / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
