#!/usr/bin/env python3
"""Generate/check the 139 cycle-form LRAT certificates excluding E1313/11.

Lean proves completeness of a pruned chain-row enumeration, checks its
conjugations into these cycle forms, and checks every LRAT certificate.
Ordinary builds never invoke a solver. --solve reconstructs all certificates.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
import json
from pathlib import Path
import subprocess
import tempfile
import time

from spectrum_small_pair_certificates import clauses, ROOT
from spectrum_63_ten_certificate import sha, TRIM

DATA = ROOT / "data/spectrum/1313_order11_refutations.json"
DEST = ROOT / "equational_theories/Spectrum/SmallPairs/OrderEleven"


def partitions(n, lower=1):
    if n == 0:
        yield []
    for k in range(lower, n + 1):
        for tail in partitions(n - k, k):
            yield [k] + tail


def cycle_rows():
    result = []
    for first in range(1, 12):
        for rest in partitions(11 - first):
            row, offset = [], 0
            for length in [first] + rest:
                row += list(range(offset + 1, offset + length)) + [offset]
                offset += length
            result.append(([first] + rest, row))
    assert len(result) == 139
    return result


def cnf(row):
    cs = clauses(1313, 11) + [[1 + y * 11 + z] for y, z in enumerate(row)]
    return (
        f"p cnf {2 * 11**3} {len(cs)}\n"
        + "".join(" ".join(map(str, c)) + " 0\n" for c in cs)
    ).encode()


def render(records):
    DEST.mkdir(parents=True, exist_ok=True)
    rows = ["![" + ",".join(map(str, r["row"])) + "]" for r in records]
    text = (
        """import equational_theories.Spectrum.SmallPairs.ChainRows
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-! Generated canonical rows: the cycle containing zero comes first; the other
cycles have nondecreasing lengths. No assertion about unenumerated permutations
is trusted here: Canonical.lean checks all rows in the proved chain enumeration. -/
namespace Spectrum.SmallPairs.OrderEleven

def row : Fin 139 → Fin 11 → Fin 11 :=
  !["""
        + ",\n    ".join(rows)
        + """]

def rows : List (Fin 11 → Fin 11) := (List.finRange 139).map row

end Spectrum.SmallPairs.OrderEleven
"""
    )
    (DEST / "Rows.lean").write_text(text)
    text = """import equational_theories.Spectrum.SmallPairs.OrderEleven.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/-! Generated saved LRAT proofs. Hashes and solver timings are in
 data/spectrum/1313_order11_refutations.json. -/
namespace Spectrum.SmallPairs.OrderEleven
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofs : Array (Array IntAction) := #[
"""
    text += ",\n".join(
        '  (parseLRATProof (include_gzip_str "../../../../'
        + r["certificate"]
        + '").toUTF8).toOption.getD #[]'
        for r in records
    )
    text += """]

@[spectrum_native]
theorem checked : ∀ i : Fin 139,
    check proofs[i.val]! (natFormula (row i)) = true := by
  native_decide

theorem unsat (i : Fin 139) : (natFormula (row i)).Unsat :=
  check_sound _ _ (checked i)

spectrum_assert unsat complete
end Spectrum.SmallPairs.OrderEleven
"""
    (DEST / "Certificates.lean").write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--jobs", type=int, default=3)
    args = parser.parse_args()
    if args.solve:
        with tempfile.TemporaryDirectory(prefix="e1313-11-") as temp:
            temp = Path(temp)

            def run(item):
                index, (cycles, row) = item
                inp, proof = temp / f"{index}.cnf", temp / f"{index}.lrat"
                inp.write_bytes(cnf(row))
                start = time.monotonic()
                r = subprocess.run(
                    [
                        "cadical",
                        "--quiet",
                        "--shrink=0",
                        "--lrat",
                        "--no-binary",
                        "-t",
                        str(args.timeout),
                        str(inp),
                        str(proof),
                    ],
                    capture_output=True,
                    text=True,
                )
                seconds = time.monotonic() - start
                if r.returncode != 20:
                    raise RuntimeError(f"No refutation for row {index}: {r.stdout}")
                print(f"row {index:03}: {seconds:.3f}s {cycles}", flush=True)
                return dict(
                    index=index,
                    row=row,
                    cycles=cycles,
                    search_seconds=round(seconds, 3),
                    cnf_sha256=sha(inp.read_bytes()),
                )

            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                records = list(pool.map(run, enumerate(cycle_rows())))
            (temp / "Trim.lean").write_text(TRIM)
            subprocess.run(
                [
                    "lake",
                    "env",
                    "lean",
                    "--run",
                    str(temp / "Trim.lean"),
                    *(str(temp / f'{r["index"]}.lrat') for r in records),
                ],
                cwd=ROOT,
                check=True,
            )
            for r in records:
                raw = (temp / f'{r["index"]}.lrat.trimmed').read_bytes()
                zipped = gzip.compress(raw, mtime=0)
                path = (
                    ROOT / f'data/spectrum/1313_eleven_lrat/row{r["index"]:03}.lrat.gz'
                )
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(zipped)
                r.update(
                    certificate=str(path.relative_to(ROOT)),
                    proof_sha256=sha(raw),
                    compressed_sha256=sha(zipped),
                    proof_bytes=len(raw),
                    compressed_bytes=len(zipped),
                )
            DATA.write_text(json.dumps(records, indent=2) + "\n")
    else:
        records = json.loads(DATA.read_text())
        assert len(records) == 139
        for (cycles, row), r in zip(cycle_rows(), records):
            assert (cycles, row) == (r["cycles"], r["row"])
            assert sha(cnf(row)) == r["cnf_sha256"]
            zipped = (ROOT / r["certificate"]).read_bytes()
            assert sha(zipped) == r["compressed_sha256"]
            assert sha(gzip.decompress(zipped)) == r["proof_sha256"]
    render(records)
    print(
        f'Verified/rendered 139 cases, {sum(r["compressed_bytes"] for r in records):,} compressed bytes.'
    )


if __name__ == "__main__":
    main()
