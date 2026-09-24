#!/usr/bin/env python3
"""Regenerate the canonical block-system reduction for E63 at order 18.

The mathematical completeness and normalization arguments are documented in
``docs/63_spectrum_progress.md``. They use previously checked order-18 short-row
exclusions; this script does not turn those arguments into Lean proofs.

Requires python-sat and networkx. All generated SAT variables represent the
finite E229 presentation; ``spectrum_63_exhaustive`` documents its translation.
"""
import sys, json, time, hashlib, gzip, subprocess, os
from pathlib import Path
import networkx as nx
from itertools import combinations
from concurrent.futures import ThreadPoolExecutor, as_completed
from spectrum_63_exhaustive import (
    base_cnf,
    case_cnf,
    variable,
    dimacs_body,
    check_model,
    add_positive_fixed_short_cycles,
    add_short_cycle_steps,
    add_even_diagonal_fibers,
    add_commuting_triangles,
    add_commuting_cycles_mod_three,
    add_nonidempotent_cycle_filter,
)
from pysat.formula import CNF
from pysat.card import CardEnc, EncType

T = [
    [0, 2, 3, 4, 1],
    [3, 1, 4, 2, 0],
    [4, 0, 2, 1, 3],
    [1, 4, 0, 3, 2],
    [2, 3, 1, 0, 4],
]


def systems():
    result = []
    pairs = list(combinations(range(6), 2))

    def add(name, inc, centers, elevated=None):
        nodes = [[] for _ in range(centers)] + [list(s) for s in inc]
        blocks = [[i for i, s in enumerate(nodes) if p in s] for p in range(6)]
        assert len(nodes) == 18 and all(len(b) == 5 for b in blocks)
        assert all(len(set(a) & set(b)) <= 1 for a, b in combinations(blocks, 2))
        degrees = [len(s) for s in nodes]
        fixed = [2 if d == 1 else 1 if d == 2 else 0 for d in degrees]
        if elevated is not None:
            fixed[elevated] += 3
        assert sum(fixed) == 18
        result.append(
            {
                "name": name,
                "blocks": blocks,
                "dual_subsets": nodes,
                "fixed_counts": fixed,
                "kind": "six_blocks",
            }
        )

    add(
        "six_triangle",
        [tuple(range(3))]
        + [p for p in pairs if not set(p) <= set(range(3))]
        + [(i,) for i in range(3)],
        2,
    )
    add("six_split_pair", [p for p in pairs if p != (0, 1)] + [(0,), (1,)], 2)
    add("six_full_center", pairs, 3, 0)
    add("six_full_edge", pairs, 3, 3)
    enumeration = enumerate_nine_block_systems()
    for g in enumeration["nine_block_configurations"]:
        for j, c in enumerate(g["configurations"]):
            result.append(
                {
                    "name": "nine_"
                    + "_".join(map(str, g["complement_cycles"]))
                    + "_"
                    + str(j),
                    "blocks": c["blocks"],
                    "dual_subsets": c["nodes_as_dual_subsets"],
                    "kind": "nine_blocks",
                }
            )
    result.append({"name": "commutative", "blocks": [], "kind": "commutative"})
    assert len(result) == 8
    return result


def common_cnf():
    f = base_cnf(18)
    add_commuting_triangles(f, 18)
    add_commuting_cycles_mod_three(f, 18)
    for x in range(18):
        f.append([-variable(18, x, y, y) for y in range(18)])
    add_nonidempotent_cycle_filter(f, 18, {"cycles": [3, 3, 4, 4, 4]})
    add_positive_fixed_short_cycles(f, 18, True, True, True)
    add_short_cycle_steps(f, 18, True)
    add_even_diagonal_fibers(f, 18)
    return f


def add_fixed_states(f, rows, total_ticks):
    ticks = []
    for x, base, width in rows:
        rowticks = list(range(f.nv + 1, f.nv + width + 1))
        f.nv += width
        ticks += rowticks
        f.extend([[-b, a] for a, b in zip(rowticks, rowticks[1:])])
        for k in range(width + 1):
            guards = (
                [rowticks[0]]
                if k == 0
                else [-rowticks[-1]] if k == width else [-rowticks[k - 1], rowticks[k]]
            )
            enc = CardEnc.equals(
                [variable(18, x, y, y) for y in range(18)],
                bound=base + 3 * k,
                top_id=f.nv,
                encoding=EncType.seqcounter,
            )
            f.extend([[*guards, *cl] for cl in enc.clauses])
    f.extend(
        CardEnc.equals(
            ticks, bound=total_ticks, top_id=f.nv, encoding=EncType.seqcounter
        ).clauses
    )


def make_cnf(common, c):
    if c["kind"] == "commutative":
        f = case_cnf(
            common,
            18,
            {"idempotent": False, "cycles": [3] * 6},
            lex_rows=3,
            lex_powers=True,
        )
    else:
        f = CNF()
        f.nv = common.nv
        f.clauses = list(common.clauses)
    nc = set()
    for block in c["blocks"]:
        b = sorted(block)
        assert len(b) == 5
        for i, x in enumerate(b):
            for j, y in enumerate(b):
                if i != j:
                    pair = tuple(sorted((x, y)))
                    nc.add(pair)
                    f.append([variable(18, x, y, b[T[i][j]])])
    for x, y in combinations(range(18), 2):
        if (x, y) not in nc:
            for z in range(18):
                f.extend(
                    [
                        [-variable(18, x, y, z), variable(18, y, x, z)],
                        [variable(18, x, y, z), -variable(18, y, x, z)],
                    ]
                )
    if c["kind"] == "six_blocks":
        assert len(nc) == 60
        for x, count in enumerate(c["fixed_counts"]):
            f.extend(
                CardEnc.equals(
                    [variable(18, x, y, y) for y in range(18)],
                    bound=count,
                    top_id=f.nv,
                    encoding=EncType.seqcounter,
                ).clauses
            )
    elif c["kind"] == "nine_blocks":
        assert len(nc) == 90
        add_fixed_states(
            f,
            [
                (x, 0, 1) if len(s) == 3 else (x, 1, 2)
                for x, s in enumerate(c["dual_subsets"])
            ],
            3,
        )
    else:
        add_fixed_states(f, [(x, 0, 5) for x in range(18)], 6)
    return f


def enumerate_nine_block_systems():
    results = []
    for cycles in [[3, 3, 3], [3, 6], [4, 5], [9]]:
        missing = nx.Graph()
        missing.add_nodes_from(range(9))
        off = 0
        for length in cycles:
            for i in range(length):
                missing.add_edge(off + i, off + (i + 1) % length)
            off += length
        edges = [e for e in combinations(range(9), 2) if not missing.has_edge(*e)]
        assert len(edges) == 27
        index = {e: i for i, e in enumerate(edges)}
        triangles = [
            t
            for t in combinations(range(9), 3)
            if all(e in index for e in combinations(t, 2))
        ]
        masks = [sum(1 << index[e] for e in combinations(t, 2)) for t in triangles]
        byedge = {i: [j for j, m in enumerate(masks) if m >> i & 1] for i in range(27)}
        covers = []

        def dfs(remaining, chosen):
            if not remaining:
                covers.append(tuple(sorted(chosen)))
                return
            candidates = min(
                (
                    [j for j in byedge[i] if masks[j] & remaining == masks[j]]
                    for i in range(27)
                    if remaining >> i & 1
                ),
                key=len,
            )
            for j in candidates:
                dfs(remaining ^ masks[j], chosen + [j])

        dfs((1 << 27) - 1, [])
        automorphisms = [
            tuple(m[i] for i in range(9))
            for m in nx.algorithms.isomorphism.GraphMatcher(
                missing, missing
            ).isomorphisms_iter()
        ]
        assert len(set(automorphisms)) == len(automorphisms)
        representatives = {}
        for cover in covers:
            ts = [triangles[i] for i in cover]
            canonical = min(
                tuple(sorted(tuple(sorted(g[x] for x in t)) for t in ts))
                for g in automorphisms
            )
            representatives.setdefault(canonical, 0)
            representatives[canonical] += 1
        configurations = []
        for ts, multiplicity in sorted(representatives.items()):
            pairs = sorted(tuple(sorted(e)) for e in missing.edges())
            nodes = [list(t) for t in ts] + [list(e) for e in pairs]
            assert len(nodes) == 18
            blocks = [[i for i, inc in enumerate(nodes) if p in inc] for p in range(9)]
            assert all(len(b) == 5 for b in blocks)
            assert all(len(set(a) & set(b)) <= 1 for a, b in combinations(blocks, 2))
            edges_nc = sorted(
                {tuple(sorted(e)) for b in blocks for e in combinations(b, 2)}
            )
            assert len(edges_nc) == 90
            stabilizer = [
                g
                for g in automorphisms
                if tuple(sorted(tuple(sorted(g[x] for x in t)) for t in ts)) == ts
            ]
            configurations.append(
                {
                    "nodes_as_dual_subsets": nodes,
                    "blocks": blocks,
                    "noncommuting_edges": edges_nc,
                    "triangles": ts,
                    "orbit_size": multiplicity,
                    "dual_automorphisms": stabilizer,
                }
            )
        results.append(
            {
                "complement_cycles": cycles,
                "raw_cover_count": len(covers),
                "automorphism_count": len(automorphisms),
                "configurations": configurations,
            }
        )
    return {
        "order": 18,
        "nine_block_configurations": results,
        "total_isomorphism_types": sum(len(r["configurations"]) for r in results),
    }


def main():
    import argparse, tempfile

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="Directory for regenerated compressed CNFs and enumeration",
    )
    parser.add_argument(
        "--verify",
        type=Path,
        help="Search manifest whose UNSAT attempts should be independently checked",
    )
    parser.add_argument(
        "--checker", type=Path, help="drat-trim executable (required with --verify)"
    )
    parser.add_argument(
        "--artifact-dir",
        type=Path,
        help="Optional extracted artifact directory, containing proofs by basename",
    )
    parser.add_argument("--seconds", type=int, default=3600)
    args = parser.parse_args()
    if args.verify and not args.checker:
        parser.error("--verify requires --checker")
    args.output.mkdir(parents=True, exist_ok=True)
    enumeration = enumerate_nine_block_systems()
    assert [r["raw_cover_count"] for r in enumeration["nine_block_configurations"]] == [
        12,
        6,
        0,
        2,
    ]
    assert enumeration["total_isomorphism_types"] == 3
    (args.output / "enumeration.json").write_text(
        json.dumps(enumeration, indent=2) + "\n"
    )
    common = common_cnf()
    cases = systems()
    manifest = json.loads(args.verify.read_text()) if args.verify else None
    if manifest:
        assert [
            {k: v for k, v in c.items() if k not in ["cnf", "cnf_sha256"]}
            for c in manifest["cases"]
        ] == cases
    attempts = (
        {a["name"]: a for a in manifest["attempts"] if a["status"] == "UNSAT_NOT_LEAN"}
        if manifest
        else {}
    )
    result = {
        "order": 18,
        "complete_canonical_cases_regenerated": True,
        "mathematical_reduction": "docs/63_spectrum_progress.md",
        "cases": [],
        "status": "PARTIAL_NOT_LEAN",
    }
    if args.checker:
        result["checker_sha256"] = hashlib.sha256(args.checker.read_bytes()).hexdigest()
    for c in cases:
        f = make_cnf(common, c)
        raw = (f"p cnf {f.nv} {len(f.clauses)}\n" + dimacs_body(f.clauses)).encode()
        digest = hashlib.sha256(raw).hexdigest()
        p = args.output / (c["name"] + ".cnf.gz")
        p.write_bytes(gzip.compress(raw, compresslevel=1))
        row = {
            **c,
            "cnf": str(p),
            "cnf_sha256": digest,
            "input_regenerated": True,
            "status": "GENERATED",
        }
        if manifest:
            assert digest == next(
                a["cnf_sha256"] for a in manifest["cases"] if a["name"] == c["name"]
            )
        if c["name"] in attempts:
            a = attempts[c["name"]]
            assert a["cnf_sha256"] == digest
            proof = Path(a["proof"])
            if args.artifact_dir:
                proof = args.artifact_dir / proof.name
            row["proof"] = str(proof)
            row["proof_sha256"] = hashlib.sha256(proof.read_bytes()).hexdigest()
            start = time.monotonic()
            with tempfile.TemporaryDirectory(
                dir=args.output, prefix="checking-"
            ) as tmp:
                inp = Path(tmp) / "input.cnf"
                inp.write_bytes(raw)
                with subprocess.Popen(
                    ["gzip", "-dc", str(proof)], stdout=subprocess.PIPE
                ) as unzip:
                    try:
                        checked = subprocess.run(
                            [str(args.checker), str(inp), "-i", "-w"],
                            stdin=unzip.stdout,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT,
                            timeout=args.seconds,
                        )
                    finally:
                        unzip.stdout.close()
                    assert unzip.wait() == 0
                (args.output / (c["name"] + ".check.log")).write_bytes(checked.stdout)
                assert checked.returncode == 0 and b"s VERIFIED" in checked.stdout
            row.update(
                status="DRAT_VERIFIED", verification_seconds=time.monotonic() - start
            )
        result["cases"].append(row)
        print(c["name"], row["status"], flush=True)
        (args.output / "proofcheck.json").write_text(
            json.dumps(result, indent=2) + "\n"
        )
    checked = {c["name"] for c in result["cases"] if c["status"] == "DRAT_VERIFIED"}
    if checked == {c["name"] for c in cases}:
        result["status"] = "ALL_EIGHT_DRAT_VERIFIED_NOT_LEAN"
    elif checked == {c["name"] for c in cases if c["kind"] != "commutative"}:
        result["status"] = "ALL_SEVEN_NONCOMMUTATIVE_CASES_DRAT_VERIFIED_NOT_LEAN"
    (args.output / "proofcheck.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
