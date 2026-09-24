#!/usr/bin/env python3
"""Enumerate and audit the commutative E229 local-unit maps at order 18.

Every row has a multiple of three fixed points, and there are eighteen fixed
points counted across all rows. Hence the local-unit map has at most six image
points. See docs/63_spectrum_progress.md for the argument and the additional
counting restrictions. The complete enumeration here deliberately includes
impossible two-cycles and large fixed-point fibers.

The script verifies only the supplied DRAT certificates. An unverified case
remains open; enumerating it does not refute it. This is not a Lean proof.
"""
import argparse, gzip, hashlib, json, subprocess, tempfile, time
from pathlib import Path
from itertools import combinations, combinations_with_replacement, permutations, product
from collections import Counter
from pysat.formula import CNF
from spectrum_63_exhaustive import (
    base_cnf,
    variable,
    dimacs_body,
    add_even_diagonal_fibers,
)
from pysat.card import CardEnc, EncType


def partitions(total, length, maximum=None):
    if not length:
        if total == 0:
            yield ()
        return
    for w in range(min(total - length + 1, maximum or total), 0, -1):
        for rest in partitions(total - w, length - 1, w):
            yield (w,) + rest


def canonical(f, weights):
    n = len(f)
    indeg = [0] * n
    children = [[] for _ in f]
    for x, y in enumerate(f):
        indeg[y] += 1
        children[y].append(x)
    queue = [x for x in range(n) if indeg[x] == 0]
    for x in queue:
        y = f[x]
        indeg[y] -= 1
        if indeg[y] == 0:
            queue.append(y)
    cyclepoints = {x for x in range(n) if indeg[x]}
    done = set()

    def tree(x):
        return (
            weights[x],
            tuple(sorted(tree(y) for y in children[x] if y not in cyclepoints)),
        )

    components = []
    for x in sorted(cyclepoints):
        if x in done:
            continue
        cycle = []
        y = x
        while y not in done:
            done.add(y)
            cycle.append(tree(y))
            y = f[y]
        components.append(min(tuple(cycle[i:] + cycle[:i]) for i in range(len(cycle))))
    return tuple(sorted(components))


def enumerate_cases():
    out = []
    for m in range(6, 0, -1):
        reps = {}
        rawcount = 0
        for weights in partitions(6, m):
            for f in product(range(m), repeat=m):
                counts = Counter(f)
                if any(counts[x] > 3 * weights[x] for x in range(m)):
                    continue
                rawcount += 1
                code = canonical(f, weights)
                if code in reps:
                    continue
                u = list(f)
                for x in range(m):
                    u += [x] * (3 * weights[x] - counts[x])
                assert len(u) == 18 and set(u) == set(range(m))
                assert Counter(u) == Counter({x: 3 * weights[x] for x in range(m)})
                reps[code] = {
                    "name": "units-" + str(m) + "-" + str(len(reps)),
                    "image_size": m,
                    "core_map": list(f),
                    "fixed_weights": list(weights),
                    "unit_map": u,
                    "canonical_code": code,
                }
        out.extend(reps.values())
    return out


def symmetry(c):
    m = c["image_size"]
    u = c["unit_map"]
    fibers = [[x for x in range(m, 18) if u[x] == a] for a in range(m)]
    out = []
    for group in fibers:
        for a, b in zip(group, group[1:]):
            g = list(range(18))
            g[a], g[b] = b, a
            out.append(g)
    autos = 0
    for core in permutations(range(m)):
        if core == tuple(range(m)):
            continue
        if any(
            c["fixed_weights"][x] != c["fixed_weights"][core[x]]
            or core[u[x]] != u[core[x]]
            for x in range(m)
        ):
            continue
        g = list(core) + [None] * (18 - m)
        for x in range(m):
            assert len(fibers[x]) == len(fibers[core[x]])
            for a, b in zip(fibers[x], fibers[core[x]]):
                g[a] = b
        assert sorted(g) == list(range(18)) and all(
            g[u[x]] == u[g[x]] for x in range(18)
        )
        out.append(g)
        autos += 1
        if autos == 8:
            break
    return out


def make_cnf(base, c, symmetry_breaking=True):
    f = CNF()
    f.nv = base.nv
    f.clauses = list(base.clauses)
    for x, e in enumerate(c["unit_map"]):
        f.append([variable(18, e, x, x)])
    if not symmetry_breaking:
        return f
    positions = list(product(range(3), range(18)))
    for g in symmetry(c):
        equal = None
        for index, (x, y) in enumerate(positions):
            guard = [] if equal is None else [-equal]
            for z in range(18):
                for w in range(z):
                    f.append(
                        [
                            *guard,
                            -variable(18, x, y, z),
                            -variable(18, g[x], g[y], g[w]),
                        ]
                    )
            if index + 1 < len(positions):
                f.nv += 1
                nxt = f.nv
                for z in range(18):
                    f.append(
                        [
                            *guard,
                            -variable(18, x, y, z),
                            -variable(18, g[x], g[y], g[z]),
                            nxt,
                        ]
                    )
                equal = nxt
    return f


def common_cnf():
    f = base_cnf(18)
    for x in range(18):
        for y in range(x + 1, 18):
            for z in range(18):
                f.extend(
                    [
                        [-variable(18, x, y, z), variable(18, y, x, z)],
                        [variable(18, x, y, z), -variable(18, y, x, z)],
                    ]
                )
    return f


def strengthen_square_units(f, c):
    """Consequences of commutativity and L_x^3=id at even order.

    Squaring is injective on each local-unit fiber. Its fibers have even
    size, and x*s(x)=u(x). See the fixed-point-fiber argument in
    docs/63_spectrum_progress.md. No closure of a fiber is assumed.
    """
    n = len(c["unit_map"])
    assert n % 2 == 0
    u = c["unit_map"]
    m = len(set(u))
    fibers = [[x for x in range(n) if u[x] == e] for e in sorted(set(u))]
    add_even_diagonal_fibers(f, n)
    for x, e in enumerate(u):
        for z in range(n):
            a = variable(n, x, x, z)
            b = variable(n, x, z, e)
            f.extend([[-a, b], [a, -b]])
        if x != e:
            f.append([-variable(n, x, x, u[e])])
    for group in fibers:
        for x, y in combinations(group, 2):
            for z in range(n):
                f.append([-variable(n, x, x, z), -variable(n, y, y, z)])
    bound = m // 2 * 2
    if max(map(len, fibers)) == n // 2:
        bound = 2
    for z in range(n):
        f.extend(
            CardEnc.atmost(
                [variable(n, x, x, z) for x in range(n)],
                bound=bound,
                top_id=f.nv,
                encoding=EncType.seqcounter,
            ).clauses
        )
    if max(map(len, fibers)) == n // 2:
        big = max(fibers, key=len)
        rest = [x for x in range(n) if x not in big]
        for x, y in combinations(rest, 2):
            for z in range(n):
                f.append([-variable(n, x, x, z), -variable(n, y, y, z)])
    return f


def audit_orbits(cases):
    """Independently check coverage using explicit permutations, not tree codes."""
    counts = {}
    for m in range(1, 7):
        expected = set()
        for ascending in combinations_with_replacement(range(1, 7), m):
            if sum(ascending) != 6:
                continue
            weights = tuple(reversed(ascending))
            for f in product(range(m), repeat=m):
                incoming = Counter(f)
                if all(incoming[x] <= 3 * weights[x] for x in range(m)):
                    expected.add((weights, f))
        covered = set()
        for c in cases:
            if c["image_size"] != m:
                continue
            own = set()
            f = c["core_map"]
            weights = c["fixed_weights"]
            for g in permutations(range(m)):
                w = [None] * m
                h = [None] * m
                for x in range(m):
                    w[g[x]] = weights[x]
                    h[g[x]] = g[f[x]]
                if w == sorted(w, reverse=True):
                    own.add((tuple(w), tuple(h)))
            assert not covered.intersection(
                own
            ), "Two proposed representatives are isomorphic"
            covered.update(own)
        assert covered == expected, "The representatives do not cover every labeled map"
        counts[m] = len(expected)
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--verify",
        type=Path,
        help="Proofcheck manifest containing cases with CNF and proof hashes",
    )
    parser.add_argument("--checker", type=Path, help="drat-trim executable")
    parser.add_argument(
        "--artifact-dir", type=Path, help="Extracted proof files, looked up by basename"
    )
    parser.add_argument(
        "--generate",
        action="append",
        default=[],
        help="Generate a named case without requiring a proof",
    )
    parser.add_argument(
        "--strengthen-square-units",
        action="store_true",
        help="Use the proved square/local-unit consequences for generated cases",
    )
    parser.add_argument(
        "--no-unit-symmetry",
        action="store_true",
        help="Omit lexicographic symmetry breaking for generated cases",
    )
    parser.add_argument("--seconds", type=int, default=3600)
    args = parser.parse_args()
    if args.verify and not args.checker:
        parser.error("--verify requires --checker")
    args.output.mkdir(parents=True, exist_ok=True)
    cases = enumerate_cases()
    assert len(cases) == 468
    counts = audit_orbits(cases)
    (args.output / "enumeration.json").write_text(
        json.dumps(
            {
                "order": 18,
                "cases": cases,
                "labeled_maps_by_image_size": counts,
                "all_orbits_independently_audited": True,
            },
            indent=2,
        )
        + "\n"
    )
    manifest = json.loads(args.verify.read_text()) if args.verify else {"cases": []}
    certs = {
        c["name"]: c for c in manifest["cases"] if c.get("status") == "DRAT_VERIFIED"
    }
    selected = set(args.generate) | set(certs)
    assert selected <= {c["name"] for c in cases}
    result = {
        "order": 18,
        "complete_case_count": 468,
        "all_orbits_independently_audited": True,
        "labeled_maps_by_image_size": counts,
        "cases": [],
        "status": "PARTIAL_NOT_LEAN",
    }
    if args.checker:
        result["checker_sha256"] = hashlib.sha256(args.checker.read_bytes()).hexdigest()
    base = common_cnf() if selected else None
    for c in cases:
        if c["name"] not in selected:
            continue
        symmetry_breaking = certs.get(c["name"], {}).get(
            "local_unit_symmetry_breaking", not args.no_unit_symmetry
        )
        f = make_cnf(base, c, symmetry_breaking=symmetry_breaking)
        strengthened = certs.get(c["name"], {}).get(
            "square_unit_strengthening", args.strengthen_square_units
        )
        if strengthened:
            strengthen_square_units(f, c)
        raw = (f"p cnf {f.nv} {len(f.clauses)}\n" + dimacs_body(f.clauses)).encode()
        digest = hashlib.sha256(raw).hexdigest()
        path = args.output / (c["name"] + ".cnf.gz")
        path.write_bytes(gzip.compress(raw, compresslevel=1))
        row = {
            "name": c["name"],
            "cnf": str(path),
            "cnf_sha256": digest,
            "input_regenerated": True,
            "status": "GENERATED",
            "square_unit_strengthening": strengthened,
            "local_unit_symmetry_breaking": symmetry_breaking,
        }
        if c["name"] in certs:
            a = certs[c["name"]]
            assert digest == a["cnf_sha256"]
            proof = Path(a["proof"])
            if args.artifact_dir:
                proof = args.artifact_dir / proof.name
            phash = hashlib.sha256(proof.read_bytes()).hexdigest()
            assert phash == a["proof_sha256"]
            started = time.monotonic()
            with tempfile.TemporaryDirectory(
                dir=args.output, prefix="checking-"
            ) as tmp:
                inp = Path(tmp) / "input.cnf"
                inp.write_bytes(raw)
                with subprocess.Popen(
                    ["xz" if proof.suffix == ".xz" else "gzip", "-dc", str(proof)],
                    stdout=subprocess.PIPE,
                ) as unzip:
                    try:
                        r = subprocess.run(
                            [str(args.checker), str(inp), "-i", "-w"],
                            stdin=unzip.stdout,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT,
                            timeout=args.seconds,
                        )
                    finally:
                        unzip.stdout.close()
                    assert unzip.wait() == 0
                (args.output / (c["name"] + ".check.log")).write_bytes(r.stdout)
                assert r.returncode == 0 and b"s VERIFIED" in r.stdout
            row.update(
                status="DRAT_VERIFIED",
                proof=str(proof),
                proof_sha256=phash,
                verification_seconds=time.monotonic() - started,
            )
        result["cases"].append(row)
        print(c["name"], row["status"], flush=True)
        (args.output / "proofcheck.json").write_text(
            json.dumps(result, indent=2) + "\n"
        )
    result["verified_count"] = sum(
        c["status"] == "DRAT_VERIFIED" for c in result["cases"]
    )
    if result["verified_count"] == 468:
        result["status"] = "ALL_468_DRAT_VERIFIED_NOT_LEAN"
    (args.output / "proofcheck.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        "Enumeration audited; verified",
        result["verified_count"],
        "of468 cases",
        flush=True,
    )


if __name__ == "__main__":
    main()
