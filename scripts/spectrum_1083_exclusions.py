#!/usr/bin/env python3
"""Reproduce and replay the E1083 exclusions at orders five and six.

Ordinary execution checks generated source and saved LRAT hashes. --search
regenerates each certificate with Lean's SAT solver, trims it, and replays it
with bv_check before installing the results. No external UNSAT answer is
accepted as a proof. --replay independently compiles the saved certificates.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

from spectrum_small_certificates import certificate

ROOT = Path(__file__).resolve().parent.parent
DEST = ROOT / "equational_theories/Spectrum/Equation1083"
DATA = ROOT / "data/spectrum/1083_small_exclusions.json"
CASES = (5, 6)
TRIM_PROGRAM = """import Lean.Elab.Tactic.BVDecide
open Std.Tactic.BVDecide.LRAT Lean.Elab.Tactic.BVDecide.LRAT
def main (args : List String) : IO Unit := do
  for file in args do
    let proof ← loadLRATProof file
    let trimmed ← IO.ofExcept (trim proof)
    dumpLRATProof file trimmed true
"""


def render(n, search=False):
    source = certificate(1083, n, timeout=60)
    old = "bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })"
    new = ("bv_decide? (config := { timeout := 60, embeddedConstraintSubst := false })"
           if search else
           f'bv_check (config := {{ embeddedConstraintSubst := false }}) "Exclusion{n}.lrat"')
    assert source.count(old) == 1
    return source.replace(old, new)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def case_record(n):
    path = DEST / f"Exclusion{n}.lrat"
    return {"law": 1083, "order": n, "theorem": f"Spectrum.not_order_1083_{n}",
            "source": str((DEST / f"Exclusion{n}.lean").relative_to(ROOT)),
            "certificate": str(path.relative_to(ROOT)),
            "certificate_bytes": path.stat().st_size,
            "certificate_sha256": digest(path),
            "equation_instances": n*n}


def lean(path, run_args=None):
    command = ["lake", "env", "lean"]
    if run_args is not None:
        command += ["--run"]
    command += [str(path)] + (run_args or [])
    subprocess.run(command, cwd=ROOT, check=True, timeout=240)


def search(n):
    with tempfile.TemporaryDirectory(prefix=f"e1083-{n}-") as tmp:
        work = Path(tmp)
        source = work / f"Exclusion{n}.lean"
        source.write_text(render(n, search=True))
        started = time.monotonic()
        lean(source)
        certificates = list(work.glob("*.lrat"))
        assert len(certificates) == 1
        lrat = work / f"Exclusion{n}.lrat"
        certificates[0].rename(lrat)
        trimmer = work / "Trim.lean"
        trimmer.write_text(TRIM_PROGRAM)
        lean(trimmer, [str(lrat)])
        source.write_text(render(n))
        lean(source)
        DEST.mkdir(parents=True, exist_ok=True)
        shutil.copy2(lrat, DEST / lrat.name)
        shutil.copy2(source, DEST / source.name)
        print(f"Order {n}: generated, trimmed, and replayed in {time.monotonic()-started:.2f}s")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--search", action="store_true")
    parser.add_argument("--replay", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    if args.search:
        for n in CASES:
            search(n)
        metadata = {
            "status": "Lean checked; registered native LRAT and encoding checks",
            "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
            "symmetry_restrictions": "none; complete tables of all magmas are covered",
            "cases": [case_record(n) for n in CASES],
        }
        DATA.write_text(json.dumps(metadata, indent=2) + "\n")
    for n in CASES:
        path = DEST / f"Exclusion{n}.lean"
        if args.write:
            path.write_text(render(n))
        assert path.read_text() == render(n), f"Stale source: {path}"
        if args.replay:
            lean(path)
    saved = json.loads(DATA.read_text())
    assert saved["cases"] == [case_record(n) for n in CASES], "Certificate metadata mismatch"
    print("Verified E1083 exclusion source, complete case coverage, and both LRAT hashes.")


if __name__ == "__main__":
    main()
