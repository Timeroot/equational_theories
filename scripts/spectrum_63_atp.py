#!/usr/bin/env python3
"""Small, exact-order E63 model searches using Vampire and/or Mace4.

Search outcomes are NOT Lean proofs. Only complete tables independently
checked against E63 are accepted as positive witnesses. In particular, a
timeout or an exhausted restricted search never supplies a spectrum exclusion.
Requires external solver executables, but no Python packages.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
# Orders 10 and 14 are computational exclusions, not yet Lean exclusions.
# Twelve further orders have replayable models in spectrum_63_bennett.py.
# Bennett (1989), Theorem 5.50, also covers 90, but this published construction has not yet been
# instantiated in the local certificates.
MISSING = [18, 26, 30, 38, 42, 90, 158]
PUBLISHED_WITHOUT_LOCAL_MODEL = [90]
LAWS = {
    63: "mul(y,mul(x,mul(x,y))) = x",
    229: "mul(mul(y,mul(y,x)),y) = x",
}


def validate(table, order, law=63):
    """Evaluate all law instances, also checking the necessary Latin property."""
    assert len(table) == order and all(len(row) == order for row in table)
    elements = set(range(order))
    assert all(type(value) is int for row in table for value in row)
    assert all(set(row) == elements for row in table)
    assert all({table[x][y] for x in range(order)} == elements for y in range(order))
    for x in range(order):
        for y in range(order):
            if law == 63:
                assert table[y][table[x][table[x][y]]] == x
            elif law == 229:
                assert table[table[y][table[y][x]]][y] == x
            else:
                raise ValueError(law)


def vampire_table(output, order):
    entries = re.findall(
        r"mul\('fmb_\$i_(\d+)','fmb_\$i_(\d+)'\)\s*=\s*'fmb_\$i_(\d+)'", output
    )
    table = [[None] * order for _ in range(order)]
    assert len(entries) == order * order, "Incomplete or unexpected Vampire model"
    for x, y, z in entries:
        x, y, z = int(x) - 1, int(y) - 1, int(z) - 1
        assert 0 <= x < order and 0 <= y < order and 0 <= z < order
        assert table[x][y] is None
        table[x][y] = z
    return table


def mace_table(output, order):
    model = re.search(
        r"interpretation\(\s*(\d+),.*?function\(mul\(_,_\),\s*\[([^]]+)\]", output, re.S
    )
    assert model and int(model[1]) == order, "Incomplete or unexpected Mace4 model"
    values = [int(x) for x in re.findall(r"\d+", model[2])]
    assert len(values) == order * order
    return [values[i : i + order] for i in range(0, len(values), order)]


def failure_status(output):
    if "Time limit" in output or "exit (max_sec_no)" in output:
        return "TIME_LIMIT"
    if "Memory limit" in output or "max_megs_no" in output:
        return "MEMORY_LIMIT"
    if "SZS status Unsatisfiable" in output or "exit (exhausted)" in output:
        return "SOLVER_EXHAUSTED_NOT_A_LEAN_EXCLUSION"
    return "SOLVER_ERROR"


def problem(
    order,
    law,
    solver,
    restriction,
    cancellation=False,
    submodel=None,
    translation_hints=False,
    first_row_cycles=None,
    all_translations=False,
):
    equations = [LAWS[law]]
    if all_translations:
        assert law == 229
        # R_y L_y^2 = id implies R_y = L_y^(-2) in the finite case.
        # Thus L_y^2 R_y = id and L_y R_y L_y = id too (E73 and E125).
        equations.extend(["mul(y,mul(y,mul(x,y))) = x", "mul(y,mul(mul(y,x),y)) = x"])
    if restriction == "pointed":
        equations.append("mul(c,c) = c")
    elif restriction == "idempotent":
        equations.append("mul(x,x) = x")
    elif restriction == "constant-diagonal":
        equations.append("mul(x,x) = c")
    if cancellation:
        equations.extend(
            ["mul(x,y) != mul(x,z) | y = z", "mul(y,x) != mul(z,x) | y = z"]
        )
    if translation_hints:
        # Finite E229 has R_x = L_x^(-2), hence L_x^3(x) = x and no
        # 2-cycles in L_x (see docs/63_spectrum_progress.md, Section 5).
        # E63 has the inverse left translations, so these hold there too.
        equations.extend(
            ["mul(x,mul(x,mul(x,x))) = x", "mul(x,mul(x,y)) != y | mul(x,y) = y"]
        )
    if first_row_cycles:
        assert sum(first_row_cycles) == order
        offset = 0
        prefix = "d" if solver == "vampire" else ""
        for length in first_row_cycles:
            for i in range(length):
                equations.append(
                    f"mul({prefix}0,{prefix}{offset + i}) = "
                    f"{prefix}{offset + (i + 1) % length}"
                )
            offset += length
    if submodel:
        k = submodel
        b = next(b for b in range(k) if (b**5 + b**4 + 1) % k == 0)
        small = [[(-(b**3) * x + b * y) % k for y in range(k)] for x in range(k)]
        validate(small, k)
        if law == 229:
            small = [[small[x].index(y) for y in range(k)] for x in range(k)]
            validate(small, k, law)
        for x in range(k):
            for y in range(k):
                prefix = "d" if solver == "vampire" else ""
                equations.append(
                    f"mul({prefix}{x},{prefix}{y}) = {prefix}{small[x][y]}"
                )
    if solver == "mace4":
        return (
            "formulas(assumptions).\n"
            + "".join(e + ".\n" for e in equations)
            + "end_of_list.\n"
        )
    equations = [re.sub(r"\b([xyz])\b", lambda m: m[1].upper(), e) for e in equations]
    source = "".join(
        f"fof(law{i},axiom,! [X,Y,Z] : ({e})).\n" for i, e in enumerate(equations)
    )
    constants = [f"d{i}" for i in range(order)]
    # Both bounds are explicit: --fmb_start_size alone permits larger models.
    source += (
        "fof(domain,axiom,! [X] : ("
        + " | ".join("X = " + c for c in constants)
        + ")).\n"
    )
    source += "fof(distinct,axiom,$distinct(" + ",".join(constants) + ")).\n"
    return source


def search(args, order, solver, law):
    stem = f"{order}-{solver}-e{law}-{args.restriction}" + (
        "-latin" if args.cancellation else ""
    )
    if args.submodel:
        stem += f"-sub{args.submodel}"
    if args.translation_hints:
        stem += "-translations"
    if args.first_row_cycles:
        stem += "-cycles-" + "-".join(map(str, args.first_row_cycles))
    all_translations = getattr(args, "all_translations", False)
    if all_translations:
        stem += "-all-translations"
    source = problem(
        order,
        law,
        solver,
        args.restriction,
        args.cancellation,
        args.submodel,
        args.translation_hints,
        args.first_row_cycles,
        all_translations,
    )
    path = args.workdir / (stem + (".p" if solver == "vampire" else ".in"))
    path.write_text(source)
    seconds = args.seconds if order <= args.large_after else args.large_seconds
    if solver == "vampire":
        command = [
            str(args.vampire),
            "-sa",
            "fmb",
            "--fmb_start_size",
            str(order),
            "--sat_solver",
            args.sat_solver,
            "-m",
            str(args.memory),
            "--random_seed",
            str(args.random_seed),
            "-t",
            str(seconds),
            str(path),
        ]
    else:
        command = [
            str(args.mace4),
            "-n",
            str(order),
            "-N",
            str(order),
            "-t",
            str(seconds),
            "-b",
            str(args.memory),
            "-O",
            str(args.mace_order),
            "-M",
            str(args.mace_measure),
            "-f",
            str(path),
        ]
    started = time.monotonic()
    record = {
        "order": order,
        "solver": solver,
        "encoding": law,
        "restriction": args.restriction,
        "cancellation": args.cancellation,
        "submodel": args.submodel,
        "translation_hints": args.translation_hints,
        "first_row_cycles": args.first_row_cycles,
        "all_translations": all_translations,
        "command": command,
        "input_sha256": hashlib.sha256(source.encode()).hexdigest(),
    }
    try:
        process = subprocess.run(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=seconds + 3,
        )
        output = process.stdout.decode(errors="replace")
        record["exit_code"] = process.returncode
        if "SZS output start FiniteModel" in output or "end of model" in output:
            table = (
                vampire_table(output, order)
                if solver == "vampire"
                else mace_table(output, order)
            )
            validate(table, order, law)
            if law == 229:
                # The left-division parastrophe is E63; verify it independently.
                table = [
                    [table[x].index(y) for y in range(order)] for x in range(order)
                ]
            validate(table, order)
            record.update(
                status="VERIFIED_MODEL",
                e63_table=table,
                idempotents=[x for x in range(order) if table[x][x] == x],
            )
        else:
            record["status"] = failure_status(output)
    except subprocess.TimeoutExpired as exc:
        output = (exc.stdout or b"").decode(errors="replace")
        record["status"] = "WALL_TIME_LIMIT"
    record["wall_seconds"] = round(time.monotonic() - started, 3)
    log = args.workdir / (stem + ".log")
    log.write_text(output)
    record["log"] = str(log)
    print(
        f'{order:3} {solver:7} E{law:<3} {record["status"]} ({record["wall_seconds"]}s)',
        flush=True,
    )
    return record


def product_closure(known, limit):
    """Record product provenance so a newly solved order can skip later searches."""
    changed = True
    while changed:
        changed = False
        for a in sorted(known):
            if a < 2:
                continue
            for b in sorted(known):
                if b < 2:
                    continue
                n = a * b
                if n > limit:
                    break
                if n not in known:
                    known[n] = {"kind": "product", "a": a, "b": b}
                    changed = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--vampire", type=Path)
    parser.add_argument("--mace4", type=Path)
    parser.add_argument("--orders", type=int, nargs="+", default=MISSING)
    parser.add_argument("--seconds", type=int, default=10)
    parser.add_argument("--large-seconds", type=int, default=5)
    parser.add_argument("--large-after", type=int, default=47)
    parser.add_argument("--memory", type=int, default=512, help="MB per solver")
    parser.add_argument(
        "--sat-solver", choices=["cadical", "minisat"], default="cadical"
    )
    parser.add_argument("--random-seed", type=int, default=1)
    parser.add_argument("--mace-order", type=int, choices=range(3), default=2)
    parser.add_argument("--mace-measure", type=int, choices=range(5), default=4)
    parser.add_argument(
        "--restriction",
        choices=["none", "pointed", "idempotent", "constant-diagonal"],
        default="none",
    )
    parser.add_argument(
        "--cancellation", action="store_true", help="Add both Latin cancellation axioms"
    )
    parser.add_argument(
        "--submodel",
        type=int,
        choices=[3, 5, 7],
        help="Restrict to extensions of a fixed affine E63 model",
    )
    parser.add_argument(
        "--translation-hints",
        action="store_true",
        help="Add consequences governing translation cycles",
    )
    parser.add_argument(
        "--all-translations",
        action="store_true",
        help="Use E73 and E125 as well as E229; requires --laws 229",
    )
    parser.add_argument(
        "--first-row-cycles",
        type=int,
        nargs="+",
        help="Fix a canonical first row; lengths must sum to the requested order",
    )
    parser.add_argument("--laws", type=int, nargs="+", choices=LAWS, default=list(LAWS))
    parser.add_argument("--workers", type=int, choices=range(1, 9), default=2)
    parser.add_argument("--workdir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--force-known",
        action="store_true",
        help="Also search known orders, for controls",
    )
    args = parser.parse_args()
    assert args.vampire or args.mace4, "Specify at least one solver executable"
    assert min(args.orders) >= 2 and args.seconds > 0 and args.large_seconds > 0
    assert args.submodel is None or args.submodel <= min(args.orders)
    assert not args.all_translations or set(args.laws) == {229}
    if args.first_row_cycles:
        assert min(args.first_row_cycles) > 0
        assert all(sum(args.first_row_cycles) == n for n in args.orders)
    args.workdir.mkdir(parents=True, exist_ok=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    certificate = json.loads((ROOT / "data/spectrum/63_constructions.json").read_text())
    known = {int(n): {"kind": "existing_construction"} for n in certificate["pointed"]}
    report = {
        "law": 63,
        "status": "MODEL_SEARCH_NOT_LEAN",
        "orders": sorted(set(args.orders)),
        "attempts": [],
        "witnesses": {},
        "derived": {},
    }
    with ThreadPoolExecutor(max_workers=args.workers) as executor:
        for n in report["orders"]:
            if n in known and not args.force_known:
                report["derived"][str(n)] = known[n]
                print(f"{n:3} skipped: {known[n]}", flush=True)
            else:
                # Finish each order before starting a larger one.
                jobs = [
                    (solver, law)
                    for solver in ["vampire", "mace4"]
                    if getattr(args, solver)
                    for law in args.laws
                ]
                records = list(executor.map(lambda job: search(args, n, *job), jobs))
                report["attempts"].extend(records)
                for record in records:
                    if (
                        record["status"] == "VERIFIED_MODEL"
                        and str(n) not in report["witnesses"]
                    ):
                        report["witnesses"][str(n)] = {
                            "e63_table": record["e63_table"],
                            "idempotents": record["idempotents"],
                            "solver": record["solver"],
                            "encoding": record["encoding"],
                        }
                        known[n] = {"kind": "verified_table", "order": n}
                product_closure(known, max(args.orders))
            args.output.write_text(json.dumps(report, indent=2) + "\n")
    print("Direct witnesses:", sorted(map(int, report["witnesses"])), flush=True)
    print("Skipped derived orders:", report["derived"], flush=True)


if __name__ == "__main__":
    main()
