#!/usr/bin/env python3
"""Regenerate and independently check the restricted E63 26/30 certificates.

Requires python-sat and DRAT-trim, but does not rerun a discovery solver.
These certificates exclude construction classes, not orders 26 or 30.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import tempfile

from spectrum_63_partial import encode

ROOT = Path(__file__).resolve().parent.parent
FAMILIES = {(25, 1), (23, 3), (22, 4), (21, 5), (29, 1), (27, 3), (26, 4), (25, 5)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "data/spectrum/63_orders26_30_proofcheck.json",
    )
    parser.add_argument(
        "--archive",
        type=Path,
        default=ROOT / "data/spectrum/63_orders26_30_certificates.tar.gz",
    )
    parser.add_argument("--checker", default="drat-trim")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    report = json.loads(args.manifest.read_text())
    families = [(f["cycle_length"], f["fixed_points"]) for f in report["families"]]
    if len(families) != len(FAMILIES) or set(families) != FAMILIES:
        raise ValueError("The manifest must cover all eight cyclic families")
    cases = report["cases"]
    names = {d["name"] for d in cases}
    if len(names) != len(cases) or any(
        not re.fullmatch(r"one-orbit-\d+-\d+-\d+|hole[68]-2", name) for name in names
    ):
        raise ValueError("Duplicate or invalid certificate names")
    if (
        hashlib.sha256(args.archive.read_bytes()).hexdigest()
        != report["archive_sha256"]
    ):
        raise ValueError("Archive hash mismatch")
    with tempfile.TemporaryDirectory(prefix="e63-cyclic-verify-") as tmp:
        output = Path(tmp)
        expected = {"hole6-2", "hole8-2"}
        for family in report["families"]:
            q, p = family["cycle_length"], family["fixed_points"]
            subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "scripts/spectrum_63_cyclic.py"),
                    str(q),
                    str(p),
                    "--generate-only",
                    "--jobs",
                    str(args.jobs),
                    "--output",
                    str(output),
                ],
                check=True,
                stdout=subprocess.DEVNULL,
            )
            shifts = json.loads((output / f"one-orbit-{q}-{p}-cases.json").read_text())
            if len(shifts) != family["case_count"]:
                raise ValueError("Canonical case count mismatch")
            expected.update(f"one-orbit-{q}-{p}-{i}" for i in range(len(shifts)))
        if expected != names:
            raise ValueError("Missing or extra cases in the proof manifest")
        for n in (6, 8):
            top, clauses = encode(
                {"order": n, "hole_size": 2, "outside_idempotent": False}
            )
            data = (
                f"p cnf {top} {len(clauses)}\n"
                + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)
            ).encode()
            (output / f"hole{n}-2.cnf.gz").write_bytes(gzip.compress(data))
        wanted = {name + ".drat.gz" for name in names}
        found = set()
        with tarfile.open(args.archive, "r:gz") as archive:
            for member in archive:
                if member.name in wanted:
                    if member.name in found or not member.isfile():
                        raise ValueError("Duplicate or invalid proof member")
                    found.add(member.name)
                    with archive.extractfile(member) as source:
                        (output / member.name).write_bytes(source.read())
        if found != wanted:
            raise ValueError("Missing proof files")

        def verify(d):
            name = d["name"]
            paths = []
            for extension, hash_key in (
                ("cnf", "cnf_sha256"),
                ("drat", "proof_sha256"),
            ):
                data = gzip.decompress((output / f"{name}.{extension}.gz").read_bytes())
                if hashlib.sha256(data).hexdigest() != d[hash_key]:
                    raise ValueError(f"Hash mismatch for {name}.{extension}")
                path = output / f"{name}.{extension}"
                path.write_bytes(data)
                paths.append(path)
            result = subprocess.run(
                [args.checker, *map(str, paths)],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=60,
            )
            if result.returncode != 0 or b"s VERIFIED" not in result.stdout:
                raise RuntimeError(
                    f"DRAT check failed: {name}\n{result.stdout.decode()}"
                )
            for path in paths:
                path.unlink()
            return name

        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            count = sum(1 for _ in pool.map(verify, cases))
        print(
            f"VERIFIED {count} restricted certificates; orders 26 and 30 remain open."
        )


if __name__ == "__main__":
    main()
