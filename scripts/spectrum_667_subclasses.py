#!/usr/bin/env python3
"""Reproduce the order-12 E667 subclass certificates.

Default: check the exact CNF and saved LRAT hashes. With --solve: regenerate
LRAT using CaDiCaL and Lean's proof trimmer. The actual theorem requires the
Lean encoding soundness proof and successful LRAT replay; UNSAT alone is not
accepted as a proof. No model search runs during an ordinary Lean build.
"""
import argparse
import gzip
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import tempfile
import time

from spectrum_63_ten_certificate import ROOT, TRIM, clauses as cubic_clauses, sha


def clauses(case):
    n = 12
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    if case == "idempotent":
        return cubic_clauses(n) + [[p(x, x, x)] for x in range(n)]
    if case != "right_identity":
        raise ValueError(case)
    q = lambda x, y, z: 1 + n**3 + (x * n + y) * n + z
    r, cs = range(n), []

    def one(v):
        cs.append(v)
        cs.extend([-a, -b] for a, b in combinations(v, 2))

    for x, y in product(r, repeat=2):
        for v in ([p(x, y, z) for z in r], [p(x, z, y) for z in r],
                  [p(z, x, y) for z in r]):
            one(v)
    for x, y in product(r, repeat=2):
        one([q(x, y, z) for z in r])
        for a, b in product(r, repeat=2):
            cs.extend([[-p(x, x, a), -p(a, y, b), q(x, y, b)],
                       [-p(x, x, a), p(a, y, b), -q(x, y, b)]])
        for a, b in product(r, repeat=2):
            cs.extend([[-q(x, y, a), -p(x, a, b), p(y, b, x)],
                       [-q(x, y, a), p(x, a, b), -p(y, b, x)]])
    for y, z in product(r, repeat=2):
        if y + 1 < z:
            cs.append([-p(0, y, z)])
    cs.extend([[p(x, 0, x)] for x in r])
    for x, z in product(r, repeat=2):
        one([q(x, y, z) for y in r])
    for z in r:
        cs.append([-p(x, x, z) for x in r])
    for x, a, b in product(r, repeat=3):
        cs.append([-p(x, x, a), -p(x, a, b), -p(x, b, x), p(x, x, x)])
    for x, a in product(r, repeat=2):
        cs.append([-p(x, x, a), -p(x, a, x), p(a, a, a)])
    for e, x, y in product(r, repeat=3):
        cs.extend([[-p(e, e, e), -p(x, x, e), -p(e, x, y), p(e, y, x)],
                   [-p(e, e, e), -p(e, x, y), -p(e, y, x), p(x, x, e)],
                   [-p(e, e, e), -p(x, x, e), -p(e, x, y), p(y, y, e)]])
    return [c for c in cs if not any(-v in c for v in c)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=("idempotent", "right_identity"), default="idempotent")
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--timeout", type=int, default=120)
    args = parser.parse_args()
    case = args.case
    base = ROOT / f"data/spectrum/667_{case}_twelve"
    data, proof_file = base.with_suffix(".json"), base.with_suffix(".lrat.gz")
    cs = clauses(case)
    variables = 12**3 * (1 if case == "idempotent" else 2)
    cnf = (f"p cnf {variables} {len(cs)}\n" +
           "".join(" ".join(map(str, c)) + " 0\n" for c in cs)).encode()
    record = json.loads(data.read_text())
    if args.solve:
        with tempfile.TemporaryDirectory(prefix="e667-subclass-") as work:
            work = Path(work)
            inp, proof = work / "input.cnf", work / "proof.lrat"
            inp.write_bytes(cnf)
            start = time.monotonic()
            result = subprocess.run(
                [args.solver, "--quiet", "--shrink=0", "--lrat", "--no-binary",
                 "-t", str(args.timeout), str(inp), str(proof)],
                capture_output=True, text=True)
            seconds = time.monotonic() - start
            if result.returncode != 20:
                raise SystemExit(f"Expected UNSAT, got {result.returncode}: {result.stdout}")
            trimmer = work / "Trim.lean"
            trimmer.write_text(TRIM)
            subprocess.run(["lake", "env", "lean", "--run", str(trimmer), str(proof)],
                           cwd=ROOT, check=True)
            payload = Path(str(proof) + ".trimmed").read_bytes()
            compressed = gzip.compress(payload, mtime=0)
            proof_file.write_bytes(compressed)
            record.update(cnf_sha256=sha(cnf), proof_sha256=sha(payload),
                          compressed_sha256=sha(compressed), clauses=len(cs),
                          variables=variables, proof_bytes=len(payload),
                          compressed_bytes=len(compressed), search_seconds=round(seconds, 3))
            data.write_text(json.dumps(record, indent=2) + "\n")
    compressed = proof_file.read_bytes()
    assert sha(cnf) == record["cnf_sha256"], "CNF changed; regenerate with --solve"
    assert sha(compressed) == record["compressed_sha256"], "Compressed proof changed"
    assert sha(gzip.decompress(compressed)) == record["proof_sha256"], "LRAT changed"
    print(f"E667/12 {case}: {len(cs):,} clauses; {len(compressed):,} compressed bytes; hashes verified.")


if __name__ == "__main__":
    main()
