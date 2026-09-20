#!/usr/bin/env python3
"""Reproduce the E1483 order-eleven SAT inputs and compressed LRAT modules.

The model-to-CNF argument and LRAT checker soundness are proved in Lean.
This independent script checks certificate hashes, the complete rank partition,
and exact reproduction of the CNFs and generated Lean modules. It does not
replace the Lean certificate checks.
"""

import argparse
import gzip
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data/definability_1483_order_eleven.json"
GENERATED = ROOT / "equational_theories/Definability/Generated"
CASES = [(2, False), (3, False)] + [(k, z) for k in range(4, 11) for z in (False, True)]


def cnf_clauses(k, zero):
    """Independent DIMACS encoding; clause order is part of the certificate."""
    assert (k, zero) in CASES
    n = 11
    R = range(n)
    base = []
    a = lambda t, x, y, z: 1 + ((t * n + x) * n + y) * n + z
    p = lambda x, y, z: a(0, x, y, z)
    r = lambda x, z: a(1, x, z, 0)
    g = lambda x, y, z: a(2, x, y, z)
    c = lambda x, z: a(3, x, z, 0)
    d = lambda x, y, z: a(4, x, y, z)
    R = range(n)
    for x, y in itertools.product(R, repeat=2):
        base.append([p(x, y, z) for z in R])
    for x, y, z, w in itertools.product(R, repeat=4):
        if z != w:
            base.append([-p(x, y, z), -p(x, y, w)])
    for y, z, b in itertools.product(R, repeat=3):
        base.append([-p(y, z, b), r(y, b)])
    for y, z, b in itertools.product(R, repeat=3):
        base.append([-p(z, y, b), c(y, b)])
    for x, y, u, b in itertools.product(R, repeat=4):
        base.append([-p(y, x, u), -r(y, b), g(x, u, b)])
    for x, u, b, v in itertools.product(R, repeat=4):
        base.append([-g(x, u, b), -p(x, b, v), p(u, v, x)])
    for x, y, u, b in itertools.product(R, repeat=4):
        base.append([-p(x, y, u), -c(y, b), d(x, u, b)])
    for x, u, b, v in itertools.product(R, repeat=4):
        base.append([-d(x, u, b), -p(b, x, v), p(v, u, x)])

    large = lambda x: a(5, x, 0, 0)
    # Reverse implications make row/column membership exact.
    for y, b in itertools.product(R, repeat=2):
        base.append([-r(y, b)] + [p(y, z, b) for z in R])
        base.append([-c(y, b)] + [p(z, y, b) for z in R])
    # Regularity of translations, proved from E1483 and its dual.
    for x, b, z in itertools.product(R, repeat=3):
        base.append([-c(x, b), -p(x, b, z), p(z, x, b)])
        base.append([-r(x, b), -p(b, x, z), p(x, z, b)])
    for x in R:
        for image in (r, c):
            base.append([-image(x, z) for z in R])
    clauses = list(base)
    for x in R:
        for image in (r, c):
            for sub in itertools.combinations(R, n - k + 1):
                clauses.append([image(x, z) for z in sub])
    image = set(range(k)) if zero else set(range(1, k + 1))
    for z in R:
        clauses.append([r(0, z) if z in image else -r(0, z)])
    for sub in itertools.combinations(R, k + 1):
        clauses.append([-c(0, z) for z in sub])
    clauses.append([p(0, 0, 0), p(0, 0, 1)] if zero else [p(0, 0, 1)])
    # Rows of rank three cannot be joined by either a row or column edge.
    if k == 3:
        for x in R:
            for im in (r, c):
                for sub in itertools.combinations(R, 8):
                    clauses.append([-large(x)] + [im(x, z) for z in sub])
            clauses.append([-p(x, x, x), large(x)])
        for x, y in itertools.product(R, repeat=2):
            clauses.append([-r(x, y), large(x), large(y)])
            clauses.append([-c(x, y), large(x), large(y)])
    for y in range(k + 1, n - 1):
        for z, w in itertools.product(range(k + 1), repeat=2):
            if z > w:
                clauses.append([-p(0, y, z), -p(0, y + 1, w)])
    # Semantically necessary cardinality bounds on both ends of every image edge.
    for threshold in [3, 4, 6]:
        flag = lambda x: a(4 + threshold, x, 0, 0)
        for x in R:
            for im in (r, c):
                for sub in itertools.combinations(R, n - threshold + 1):
                    clauses.append([-flag(x)] + [im(x, z) for z in sub])
    for x in R:
        clauses.append([-p(x, x, x), a(8, x, 0, 0)])
    for x, y in itertools.product(R, repeat=2):
        for im in (r, c):
            for t, u in [(3, 6), (4, 4), (6, 3)]:
                clauses.append([-im(x, y), a(4 + t, x, 0, 0), a(4 + u, y, 0, 0)])
    clauses = [cl for cl in clauses if not any(-l in cl for l in cl)]
    return clauses


def cnf_bytes(k, zero):
    clauses = cnf_clauses(k, zero)
    header = f"p cnf {11**4} {len(clauses)}\n"
    return (header + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)).encode()


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def case_name(k, zero):
    return f"Rank{k}Zero{int(zero)}"


def render_case(case):
    name = case_name(case["rank"], case["zero_in_image"])
    zero = "true" if case["zero_in_image"] else "false"
    path = "../../../" + case["certificate"]
    text = f"""import equational_theories.Definability.Central1483SAT
import equational_theories.Definability.IncludeGzip

/-! Generated by scripts/definability_1483_sat_check.py.
Compressed certificate SHA-256: {case["compressed_sha256"]}
Expanded certificate SHA-256: {case["proof_sha256"]}
CNF SHA-256: {case["cnf_sha256"]}
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

namespace Magma.Central1483.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proof{name} : Array IntAction :=
  (parseLRATProof (include_gzip_str "{path}").toUTF8).toOption.getD #[]

theorem check{name} :
    check proof{name} (CNF.natRankFormula 11 {case["rank"]} {zero}) = true := by
  native_decide

theorem unsat{name} : (CNF.natRankFormula 11 {case["rank"]} {zero}).Unsat :=
  check_sound proof{name} _ check{name}

"""
    declaration = "Magma.Central1483.Refutation.unsat" + name
    axioms = case.get("axioms", {}).get(declaration)
    if axioms:
        text += f"/-- info: {axioms} -/\n#guard_msgs in\n"
    text += f"#print axioms unsat{name}\n\nend Magma.Central1483.Refutation\n"
    return text


def validate(case, export=None):
    k, zero = case["rank"], case["zero_in_image"]
    data = cnf_bytes(k, zero)
    assert sha256(data) == case["cnf_sha256"], (k, zero, "CNF hash")
    assert len(data.splitlines()) - 1 == case["clauses"]
    if export is not None:
        export.mkdir(parents=True, exist_ok=True)
        (export / (case_name(k, zero) + ".cnf")).write_bytes(data)
    certificate = ROOT / case["certificate"]
    compressed = certificate.read_bytes()
    assert sha256(compressed) == case["compressed_sha256"], certificate
    digest = hashlib.sha256()
    size = 0
    count = 0
    last = None
    # Trimming leaves only RUP additions, with consecutive identifiers.
    # Check the proof graph structure independently of the Lean parser.
    with gzip.open(certificate, "rb") as stream:
        for line in stream:
            digest.update(line)
            size += len(line)
            words = list(map(int, line.split()))
            assert words[0] == case["clauses"] + count + 1
            cut = words.index(0, 1)
            assert words[-1] == 0
            assert all(0 < h < words[0] for h in words[cut + 1 : -1])
            assert all(0 < abs(lit) <= 11**4 for lit in words[1:cut])
            assert cut > 1 or count + 1 == case["proof_steps"]
            count += 1
            last = words
    assert digest.hexdigest() == case["proof_sha256"], certificate
    assert size == case["proof_bytes"] and count == case["proof_steps"]
    assert last is not None and last[1] == 0
    print(
        f"{case_name(k, zero)}: {case['clauses']} CNF clauses; {count} LRAT additions; hashes checked.",
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument(
        "--allow-partial",
        action="store_true",
        help="development only: allow an incomplete certificate partition",
    )
    parser.add_argument("--only", help="one case name, such as Rank3Zero0")
    parser.add_argument("--export-cnf", type=Path)
    args = parser.parse_args()
    manifest = json.loads(DATA.read_text())
    cases = manifest["cases"]
    keys = [(c["rank"], c["zero_in_image"]) for c in cases]
    assert len(set(keys)) == len(keys) and set(keys) <= set(CASES)
    if not args.allow_partial:
        assert set(keys) == set(CASES), "certificate partition is incomplete"
    matched = 0
    for case in cases:
        name = case_name(case["rank"], case["zero_in_image"])
        if args.only and name != args.only:
            continue
        matched += 1
        validate(case, args.export_cnf)
        path = GENERATED / ("Central1483" + name + ".lean")
        rendered = render_case(case)
        if args.write:
            path.write_text(rendered)
        else:
            assert path.read_text() == rendered, path
    assert matched, "no matching certificate case"
    print(f"Checked {matched} certificate cases and generated modules.")


if __name__ == "__main__":
    main()
