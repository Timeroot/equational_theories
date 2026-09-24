#!/usr/bin/env python3
"""Search/check partial E229 tables; assemble three conditional E63 158-models.

Checking and assembly use only the standard library. Search requires python-sat
and a CaDiCaL executable. Search failures are never E63 spectrum exclusions.
See docs/63_order158_search.md for the definitions and construction arguments.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_63_atp import validate
from spectrum_63_bennett import gf_affine, glue, prime, product, singular, td


def layout(spec):
    """Return hole membership; None denotes an ordinary (non-hole) point."""
    if "sizes" in spec:
        sizes = spec["sizes"]
        if not sizes or any(type(s) is not int or s < 1 for s in sizes):
            raise ValueError("Hole sizes must be positive integers")
        return [i for i, size in enumerate(sizes) for _ in range(size)]
    n, h = spec["order"], spec["hole_size"]
    if type(n) is not int or type(h) is not int or not 0 < h < n:
        raise ValueError("Require 0 < hole_size < order")
    return [0] * h + [None] * (n - h)


def same_hole(owner, x, y):
    return owner[x] is not None and owner[x] == owner[y]


def check(spec):
    """Check every defined cell, Latin condition, and E229 instance directly."""
    owner = layout(spec)
    n = len(owner)
    table = spec["table"]
    if len(table) != n or any(len(row) != n for row in table):
        raise ValueError("Wrong table dimensions")
    for x in range(n):
        for y in range(n):
            z = table[x][y]
            if same_hole(owner, x, y):
                if z is not None:
                    raise ValueError("Hole cells must be null")
            elif type(z) is not int or not 0 <= z < n:
                raise ValueError("Missing or invalid defined entry")
        expected = {y for y in range(n) if not same_hole(owner, x, y)}
        if {z for z in table[x] if z is not None} != expected:
            raise ValueError("Incorrect row symbols")
        if {table[y][x] for y in range(n) if table[y][x] is not None} != expected:
            raise ValueError("Incorrect column symbols")
        if spec.get("outside_idempotent") and owner[x] is None and table[x][x] != x:
            raise ValueError("An ordinary point is not idempotent")
    for x in range(n):
        for y in range(n):
            if same_hole(owner, x, y):
                continue
            a = table[y][x]
            b = table[y][a]
            if b is None or table[b][y] != x:
                raise ValueError(f"E229 fails at ({x}, {y})")
    return table


def encode(spec):
    from pysat.card import CardEnc, EncType

    owner = layout(spec)
    n = len(owner)
    top, clauses = n**3, []

    def var(x, y, z):
        return 1 + (x * n + y) * n + z

    def exactly(values):
        nonlocal top
        c = CardEnc.equals(values, 1, top_id=top, encoding=EncType.seqcounter)
        top = c.nv
        clauses.extend(c.clauses)

    allowed = {}
    for x in range(n):
        for y in range(n):
            zs = [] if same_hole(owner, x, y) else [
                z for z in range(n)
                if not same_hole(owner, x, z) and not same_hole(owner, y, z)
            ]
            allowed[x, y] = zs
            if not same_hole(owner, x, y):
                exactly([var(x, y, z) for z in zs])
            clauses.extend([-var(x, y, z)] for z in range(n) if z not in zs)
    for x in range(n):
        for z in range(n):
            if not same_hole(owner, x, z):
                exactly([var(x, y, z) for y in range(n) if not same_hole(owner, x, y)])
                exactly([var(y, x, z) for y in range(n) if not same_hole(owner, x, y)])
        if spec.get("outside_idempotent") and owner[x] is None:
            clauses.append([var(x, x, x)])
    for x in range(n):
        for y in range(n):
            for a in allowed[y, x]:
                for b in allowed[y, a]:
                    clauses.append([-var(y, x, a), -var(y, a, b), var(b, y, x)])
    return top, clauses


def search(spec, output, solver, seconds):
    output.mkdir(parents=True, exist_ok=True)
    top, clauses = encode(spec)
    cnf = output / "input.cnf"
    with cnf.open("w") as f:
        f.write(f"p cnf {top} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    start = time.monotonic()
    command = [solver, "-t", str(seconds), str(cnf)]
    with (output / "solver.log").open("w") as f:
        try:
            r = subprocess.run(command, stdout=f, stderr=subprocess.STDOUT, timeout=seconds + 30)
            code = r.returncode
        except subprocess.TimeoutExpired:
            code = None
    result = dict(spec, status="UNRESOLVED", exit_code=code,
                  seconds=time.monotonic() - start, command=command,
                  cnf_sha256=hashlib.sha256(cnf.read_bytes()).hexdigest())
    if code == 20:
        result["status"] = "UNSAT_RESTRICTED_NO_CERTIFICATE"
    elif code == 10:
        vals = {int(v) for line in (output / "solver.log").read_text().splitlines()
                if line.startswith("v ") for v in line.split()[1:] if int(v) > 0}
        owner = layout(spec)
        n = len(owner)
        result["table"] = [
            [None if same_hole(owner, x, y) else
             next(z for z in range(n) if 1 + (x * n + y) * n + z in vals)
             for y in range(n)] for x in range(n)
        ]
        check(result)
        result["status"] = "VERIFIED_PARTIAL_MODEL"
    elif code not in (None, 0):
        result["status"] = "SOLVER_ERROR"
    (output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])


def inflate(groups, blocks, weights, fillers, partials):
    """Wilson-style inflation: fill groups, then transversal partial tables."""
    points = [(x, a) for g in groups for x in g for a in range(weights[x])]
    index = {p: i for i, p in enumerate(points)}
    n = len(points)
    table = [[-1] * n for _ in range(n)]

    def put(x, y, z):
        if table[x][y] != -1:
            raise ValueError("Overlapping fillings")
        table[x][y] = z

    for group, f in zip(groups, fillers, strict=True):
        mapping = [index[x, a] for x in group for a in range(weights[x])]
        validate(f, len(mapping), 229)
        for i, x in enumerate(mapping):
            for j, y in enumerate(mapping):
                put(x, y, mapping[f[i][j]])
    for block in blocks:
        sizes = tuple(weights[x] for x in block if weights[x])
        spec = {"sizes": list(sizes), "table": partials[sizes]}
        f = check(spec)
        owner = layout(spec)
        mapping = [index[x, a] for x in block for a in range(weights[x])]
        for i, x in enumerate(mapping):
            for j, y in enumerate(mapping):
                if owner[i] != owner[j]:
                    put(x, y, mapping[f[i][j]])
    validate(table, n, 229)
    return table


def assemble(spec):
    q = [row[:] for row in check(spec)]
    n = len(q)
    small = {3: prime(3, False), 4: gf_affine(4, 7, 2, 2), 5: prime(5),
             7: prime(7), 8: gf_affine(8, 11, 4, 5), 11: prime(11)}
    if (n, spec.get("hole_size")) == (34, 3):
        for x in range(3):
            for y in range(3):
                q[x][y] = small[3][x][y]
        validate(q, 34, 229)
        table = singular(small[5], q, prime(31, False), p=3)
        method = "5*(34-3)+3 singular product"
    elif (n, spec.get("hole_size")) == (25, 6):
        g, b = td(19, 8)
        table = glue(g, b, 6, [q] * 7 + [product(small[5], small[5])], small)
        method = "TD(8,19), seven partial 25-models, a full 25-model; six common points"
    elif spec.get("sizes") == [3] * 7 + [2]:
        g, b = td(7, 8)
        weights = {x: 3 for group in g for x in group}
        for i, x in enumerate(g[-1]):
            weights[x] = 3 if i < 3 else 2 if i == 3 else 0
        partials = {}
        for k in (7, 8):
            f = product(small[k], small[3])
            partials[(3,) * k] = [
                [None if x // 3 == y // 3 else f[x][y] for y in range(3 * k)]
                for x in range(3 * k)
            ]
        partials[(3,) * 7 + (2,)] = q
        model21 = singular(small[5], small[5], small[4])
        table = inflate(g, b, weights, [model21] * 7 + [small[11]], partials)
        method = "Weighted TD(8,7), partial tables of type 3^7 2^1, group sizes 21^7 11^1"
    else:
        raise ValueError("Not an ingredient for one of the three order-158 constructions")
    validate(table, 158, 229)
    e63 = [[row.index(y) for y in range(158)] for row in table]
    validate(e63, 158, 63)
    return {"law": 63, "order": 158, "status": "DIRECTLY_CHECKED_MODEL_NOT_LEAN",
            "construction": method, "ingredient": spec, "e63_table": e63,
            "table_sha256": hashlib.sha256(json.dumps(e63, separators=(",", ":")).encode()).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("search")
    shape = p.add_mutually_exclusive_group(required=True)
    shape.add_argument("--hole", nargs=2, type=int, metavar=("ORDER", "HOLE_SIZE"))
    shape.add_argument("--sizes", type=lambda s: [int(x) for x in s.split(",")])
    p.add_argument("--outside-idempotent", action="store_true")
    p.add_argument("--solver", default="cadical")
    p.add_argument("--seconds", type=int, default=300)
    p.add_argument("--output", type=Path, required=True)
    for name in ("check", "assemble"):
        p = sub.add_parser(name)
        p.add_argument("certificate", type=Path)
        if name == "assemble":
            p.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "search":
        if args.seconds < 1:
            parser.error("--seconds must be positive")
        if args.sizes is not None and args.outside_idempotent:
            parser.error("--outside-idempotent applies only to a single-hole table")
        spec = ({"sizes": args.sizes} if args.sizes is not None else
                {"order": args.hole[0], "hole_size": args.hole[1],
                 "outside_idempotent": args.outside_idempotent})
        search(spec, args.output, args.solver, args.seconds)
    else:
        spec = json.loads(args.certificate.read_text())
        if args.command == "check":
            check(spec)
            print("VERIFIED_PARTIAL_MODEL (not a Lean proof)")
        else:
            result = assemble(spec)
            args.output.write_text(json.dumps(result, indent=2) + "\n")
            print("VERIFIED E63 ORDER 158", result["table_sha256"])


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Do not disable assertions when running certificate checkers")
    main()
