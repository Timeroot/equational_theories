#!/usr/bin/env python3
"""Check, or reproduce, the compact idempotent E667/13 refutation.

Normal builds replay saved data; no discovery solver runs during a Lean build.
Use --solve --workdir PATH to regenerate with CaDiCaL, Lean's LRAT trimmer,
and the existing compact-RUP encoder. The Lean theorem checks the output.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import time

from spectrum_63_ten_certificate import ROOT, TRIM, clauses

DATA = ROOT / "data/spectrum/667_idempotent_thirteen.json"
PROOF = ROOT / "data/spectrum/667_idempotent_thirteen.rup.gz"


def sha(data):
    return hashlib.sha256(data).hexdigest()


def cnf():
    cs = clauses(13) + [[1 + (x*13+x)*13+x] for x in range(13)]
    return (f"p cnf {13**3} {len(cs)}\n" +
            "".join(" ".join(map(str, c))+" 0\n" for c in cs)).encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--workdir", type=Path)
    args = parser.parse_args()
    payload = cnf()
    if args.solve:
        if args.workdir is None:
            parser.error("--solve requires an explicit --workdir")
        w = args.workdir.resolve()
        w.mkdir(parents=True, exist_ok=True)
        inp, raw = w / "input.cnf", w / "proof.lrat"
        inp.write_bytes(payload)
        started = time.monotonic()
        r = subprocess.run(["cadical", "--quiet", "--shrink=0", "--lrat",
                            "--no-binary", "-t", "30", str(inp), str(raw)],
                           capture_output=True, text=True, timeout=40)
        assert r.returncode == 20, (r.returncode, r.stdout, r.stderr)
        seconds = time.monotonic() - started
        (w / "Trim.lean").write_text(TRIM.replace("trimmed false", "trimmed true"))
        subprocess.run(["lake", "env", "lean", "--run", str(w / "Trim.lean"), str(raw)],
                       cwd=ROOT, check=True)
        exe = w / "compact-rup"
        subprocess.run(["g++", "-O2", "-std=c++17",
                        str(ROOT / "scripts/spectrum_compact_rup.cpp"), "-o", str(exe)], check=True)
        compact = w / "proof.rup"
        with Path(str(raw)+".trimmed").open("rb") as source:
            subprocess.run([str(exe), str(compact)], stdin=source, check=True)
        compressed = gzip.compress(compact.read_bytes(), mtime=0)
        PROOF.write_bytes(compressed)
        record = dict(law=667, order=13, restriction="idempotent",
                      status="CERTIFICATE_GENERATED_AWAITING_LEAN_REPLAY",
                      theorem="Spectrum.E667.not_idempotent_thirteen",
                      format="Compact RUP v1; replayed by Lean verified LRAT checker",
                      variables=13**3, clauses=129688, search_seconds=round(seconds, 3),
                      cnf_sha256=sha(payload), compact_sha256=sha(compact.read_bytes()),
                      compressed_bytes=len(compressed), compressed_sha256=sha(compressed))
        DATA.write_text(json.dumps(record, indent=2)+"\n")
    record = json.loads(DATA.read_text())
    compressed = PROOF.read_bytes()
    assert sha(payload) == record["cnf_sha256"], "CNF changed"
    assert sha(compressed) == record["compressed_sha256"], "Compressed proof changed"
    assert sha(gzip.decompress(compressed)) == record["compact_sha256"], "Compact proof changed"
    print(f"E667 idempotent order 13: encoding and {len(compressed):,}-byte certificate hashes verified.")


if __name__ == "__main__":
    main()
