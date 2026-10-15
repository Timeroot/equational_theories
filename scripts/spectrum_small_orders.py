#!/usr/bin/env python3
"""Reproduce the order-eight/ten chain-law exclusions.

The shared Lean encoding proves soundness, finite cancellation, and symmetry
reduction. CaDiCaL supplies data only; Lean checks every saved LRAT certificate.
Run --solve to regenerate certificates, or without arguments to verify hashes
and regenerate their Lean wrappers. Solver timeouts never create exclusions.
"""
import argparse
import gzip
from itertools import combinations, permutations, product
import json
import lzma
from pathlib import Path
import subprocess
import time

from spectrum_63_ten_certificate import ROOT, TRIM, sha

DATA = ROOT / "data/spectrum/small_orders_20261007.json"
DEST = ROOT / "equational_theories/Spectrum/SmallOrders/Certificates"
CASES = [
    (670, 8),
    (1076, 8),
    (1286, 8),
    (467, 10),
    (704, 10),
    (1076, 10),
    (1110, 10),
    (1279, 10),
    (1286, 10),
    (1313, 10),
    (1516, 10),
    (907, 10),
    (1083, 10),
]
LAWS = (467, 670, 677, 704, 1076, 1083, 1110, 1279, 1286, 1313)
RIGHT = (704, 1076, 1083, 1110, 1279, 1286, 1313)


def clauses907(n):
    """E907 with proved finite cancellation and pointed-cycle exclusions."""
    r = range(n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    cs = []
    for x, y in product(r, repeat=2):
        for vs in ([p(x, y, z) for z in r], [p(x, z, y) for z in r]):
            cs.append(vs)
            cs.extend([-a, -b] for a, b in combinations(vs, 2))
    for x, y, a, b, c in product(r, repeat=5):
        cs.extend(
            [
                [-p(y, x, a), -p(x, y, b), -p(a, b, c), p(y, c, x)],
                [-p(y, x, a), -p(x, y, b), p(a, b, c), -p(y, c, x)],
            ]
        )
    for x in r:
        cs.append([-p(0, 0, 0), p(x, x, x)])
    for y, z in product(r, repeat=2):
        if z > y + 1:
            cs.append([-p(0, y, z)])
    for a in r:
        for k in (2, 3, 4):
            for tail in permutations([b for b in r if a != b], k - 1):
                cycle = (a, *tail, a)
                cs.append([-p(a, cycle[j], cycle[j + 1]) for j in range(k)])
    return [c for c in cs if not any(-v in c for v in c)]


def variables(law, n):
    return n**3 if law == 907 else 2 * n**3


def base_clauses(law, n):
    if law == 907:
        return clauses907(n)
    assert (law in LAWS or law == 1516) and n > 0
    r = range(n)
    p = lambda x, y, z: 1 + (x * n + y) * n + z
    q = lambda x, y, z: 1 + n**3 + (x * n + y) * n + z
    cs = []

    def one(v):
        cs.append(v)
        cs.extend([-a, -b] for a, b in combinations(v, 2))

    for x, y in product(r, repeat=2):
        one([p(x, y, z) for z in r])
        one([p(x, z, y) for z in r])
        if law in RIGHT or law == 1516:
            one([p(z, x, y) for z in r])
    for x, y in product(r, repeat=2):
        one([q(x, y, z) for z in r])
        if law == 1516:
            for a, b in product(r, repeat=2):
                av, bv, cv = p(x, y, a), p(x, a, b), q(x, y, b)
                cs.extend([[-av, -bv, cv], [-av, bv, -cv], [av, -bv, -cv]])
            for a, b in product(r, repeat=2):
                av, bv, cv = p(y, y, a), q(x, y, b), p(a, b, x)
                cs.extend([[-av, -bv, cv], [-av, bv, -cv]])
            continue
        first = (
            (y, y)
            if law == 467
            else (
                (x, y)
                if law in (670, 1076, 1286)
                else (y, x) if law in (677, 1083, 1313) else (x, x)
            )
        )
        for a, b in product(r, repeat=2):
            inner = (
                (x, a)
                if law in (467, 1076, 1083)
                else (
                    (y, a) if law == 1110 else (a, x) if law in (1286, 1313) else (a, y)
                )
            )
            av, bv, cv = p(*first, a), p(*inner, b), q(x, y, b)
            cs.extend([[-av, -bv, cv], [-av, bv, -cv]])
            if law not in (670, 677):
                cs.append([av, -bv, -cv])
        for a, b in product(r, repeat=2):
            last = (
                (x, a) if law in (467, 670, 677) else (y, a) if law == 704 else (a, y)
            )
            av, bv, cv = q(x, y, a), p(*last, b), p(y, b, x)
            cs.extend([[-av, -bv, cv], [-av, bv, -cv], [av, -bv, -cv]])
    for x in r:
        cs.append([-p(0, 0, 0), p(x, x, x)])
    for y, z in product(r, repeat=2):
        if z > y + 1:
            cs.append([-p(0, y, z)])
    if law in (704, 1110, 1279, 1516):
        for y in r:
            one([p(x, x, y) for x in r])
    return [c for c in cs if not any(-v in c for v in c)]


def clauses(law, n):
    cs = base_clauses(law, n)
    if law == 1083:
        p = lambda x, y, z: 1 + (x * n + y) * n + z
        cs.extend(
            [p(0, 0, 0), -p(0, y, y), -p(0, z, z)] for y, z in combinations(range(n), 2)
        )
    return [c for c in cs if not any(-v in c for v in c)]


def cnf_bytes(law, n):
    cs = clauses(law, n)
    return (
        f"p cnf {variables(law, n)} {len(cs)}\n"
        + "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
    ).encode()


def render(r):
    law, n = r["law"], r["order"]
    module = "SmallOrders." + ("SquareOuter" if law == 1516 else "Encoding")
    formula = (
        f"SquareOuter.natFormula {n}"
        if law == 1516
        else f"Encoding.natFormula .e{law} {n}"
    )
    bridge = (
        "SmallOrders.SquareOuter.not_hasModel"
        if law == 1516
        else f"SmallOrders.Encoding.not_hasModel .e{law}"
    )
    if law == 907:
        module = "Equation907.OrderTen.Encoding"
        formula = "E907.OrderTen.Encoding.natFormula"
        bridge = "E907.OrderTen.Encoding.not_hasModel"
    if law == 1083:
        module = "SmallOrders.FewFixedEncoding"
        formula = f"FewFixedEncoding.natFormula .e1083 {n}"
        bridge = "SmallOrders.FewFixedEncoding.not_hasModel .e1083 (Or.inr rfl)"
    imports = "import equational_theories.Definability.IncludeGzip"
    proof = f"""(parseLRATProof (include_gzip_str
    "../../../../{r['certificate']}").toUTF8).toOption.getD #[]"""
    if r.get("format") in ("compact-rup-xz", "binary-lrat-xz"):
        imports = (
            "import SpectrumCertificateData\nimport SpectrumCertificateData.Replay"
        )
        embedded = f"""(include_binary_xz "../../../../{r['certificate']}")"""
        proof = (
            f"Spectrum.CertificateData.CompactRup.reconstruct {embedded} ({formula})"
            if r["format"] == "compact-rup-xz"
            else f"(parseLRATProof {embedded}).toOption.getD #[]"
        )
    options = (
        "set_option maxRecDepth 65536\nset_option maxHeartbeats 0\n"
        if r.get("format")
        else ""
    )
    payload_label = "Expanded certificate" if r.get("format") else "Expanded LRAT"
    return f"""import equational_theories.Spectrum.{module}
{imports}
import equational_theories.Spectrum.Status

/- Generated by scripts/spectrum_small_orders.py.
CNF SHA-256: {r['cnf_sha256']}
{payload_label} SHA-256: {r['proof_sha256']}
All normalization and encoding steps are proved in Lean; the solver supplies
only a certificate checked by Lean's verified LRAT checker. -/
{options}namespace Spectrum.SmallOrders.E{law}N{n}
open Std.Sat Std.Tactic.BVDecide LRAT

private def proof : Array IntAction :=
  {proof}

@[spectrum_native]
theorem checked : check proof ({formula}) = true := by
  native_decide

theorem unsat : ({formula}).Unsat := check_sound proof _ checked
end Spectrum.SmallOrders.E{law}N{n}

namespace Spectrum
theorem not_order_{law}_{n} : ¬ Law{law}.HasModel {n} :=
  {bridge} SmallOrders.E{law}N{n}.unsat

spectrum_assert not_order_{law}_{n} complete
end Spectrum
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--solve", action="store_true")
    ap.add_argument(
        "--only",
        type=int,
        help="With --solve, regenerate only this law; retain the other verified records",
    )
    ap.add_argument("--seconds", type=int, default=600)
    args = ap.parse_args()
    if args.seconds <= 0:
        ap.error("--seconds must be positive")
    if args.only is not None and (
        not args.solve or args.only not in {law for law, _ in CASES}
    ):
        ap.error("--only requires --solve and a law with a saved certificate")
    DEST.mkdir(parents=True, exist_ok=True)
    if args.solve:
        work = ROOT / ".cache/small-orders-20261007/certificates"
        work.mkdir(parents=True, exist_ok=True)
        trim = work / "Trim.lean"
        trim.write_text(TRIM)
        trim_binary = work / "TrimBinary.lean"
        trim_binary.write_text(TRIM.replace("trimmed false", "trimmed true"))
        packer = work / "compact-rup"
        records = []
        previous = (
            {(r["law"], r["order"]): r for r in json.loads(DATA.read_text())}
            if args.only and DATA.exists()
            else {}
        )
        for law, n in CASES:
            if args.only and law != args.only:
                r = previous[law, n]
                assert sha(cnf_bytes(law, n)) == r["cnf_sha256"]
                assert (
                    sha((ROOT / r["certificate"]).read_bytes())
                    == r["compressed_sha256"]
                )
                records.append(r)
                continue
            stem = work / f"e{law}_{n}"
            cnf = cnf_bytes(law, n)
            stem.with_suffix(".cnf").write_bytes(cnf)
            start = time.monotonic()
            out = subprocess.run(
                [
                    "cadical",
                    "--quiet",
                    "--shrink=0",
                    "--lrat",
                    "--no-binary",
                    "-t",
                    str(args.seconds),
                    str(stem.with_suffix(".cnf")),
                    str(stem.with_suffix(".lrat")),
                ],
                capture_output=True,
                text=True,
                timeout=args.seconds + 15,
            )
            stem.with_suffix(".log").write_text(out.stdout + out.stderr)
            if out.returncode != 20:
                raise SystemExit(
                    f"E{law}/{n}: no complete refutation (return code {out.returncode}); no certificate installed."
                )
            elapsed = time.monotonic() - start
            subprocess.run(
                [
                    "lake",
                    "env",
                    "lean",
                    "--run",
                    str(trim_binary if law in (907, 1083) else trim),
                    str(stem.with_suffix(".lrat")),
                ],
                cwd=ROOT,
                check=True,
            )
            payload = Path(str(stem.with_suffix(".lrat")) + ".trimmed").read_bytes()
            if law in (907, 1083):
                if (
                    not packer.exists()
                    or (ROOT / "scripts/spectrum_compact_rup.cpp").stat().st_mtime
                    > packer.stat().st_mtime
                ):
                    subprocess.run(
                        [
                            "g++",
                            "-O3",
                            "-std=c++17",
                            str(ROOT / "scripts/spectrum_compact_rup.cpp"),
                            "-o",
                            str(packer),
                        ],
                        check=True,
                    )
                compact = stem.with_suffix(".rup")
                with Path(str(stem.with_suffix(".lrat")) + ".trimmed").open(
                    "rb"
                ) as inp:
                    subprocess.run(
                        [str(packer), "--input-mask", str(compact)],
                        stdin=inp,
                        check=True,
                    )
                payload = compact.read_bytes()
                zipped = lzma.compress(payload, preset=6)
                dest = ROOT / f"data/spectrum/order_ten_rup/e{law}_{n}.rup.xz"
            else:
                zipped = gzip.compress(payload, mtime=0)
                dest = ROOT / f"data/spectrum/small_orders_lrat/e{law}_{n}.lrat.gz"
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(zipped)
            r = dict(
                law=law,
                order=n,
                theorem=f"Spectrum.not_order_{law}_{n}",
                variables=variables(law, n),
                clauses=len(clauses(law, n)),
                cnf_sha256=sha(cnf),
                proof_sha256=sha(payload),
                compressed_sha256=sha(zipped),
                proof_bytes=len(payload),
                compressed_bytes=len(zipped),
                search_seconds=round(elapsed, 3),
                certificate=str(dest.relative_to(ROOT)),
                checking="Lean LRAT.check_sound with registered native_decide; no sorry",
            )
            if law in (907, 1083):
                r["format"] = "compact-rup-xz"
            records.append(r)
            print(
                f"E{law}/{n}: {elapsed:.3f}s search; {len(zipped):,} compressed bytes",
                flush=True,
            )
            (DEST / f"E{law}N{n}.lean").write_text(render(r))
        DATA.write_text(json.dumps(records, indent=2) + "\n")
    else:
        records = json.loads(DATA.read_text())
        assert [(r["law"], r["order"]) for r in records] == CASES
        for r in records:
            zipped = (ROOT / r["certificate"]).read_bytes()
            assert sha(cnf_bytes(r["law"], r["order"])) == r["cnf_sha256"]
            assert sha(zipped) == r["compressed_sha256"]
            unpacked = (
                lzma.decompress(zipped)
                if r["certificate"].endswith(".xz")
                else gzip.decompress(zipped)
            )
            assert sha(unpacked) == r["proof_sha256"]
            (DEST / f"E{r['law']}N{r['order']}.lean").write_text(render(r))
        print(f"Verified {len(records)} encodings and saved certificate hashes.")


if __name__ == "__main__":
    main()
