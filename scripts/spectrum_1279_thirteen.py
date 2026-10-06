#!/usr/bin/env python3
"""Generate/check the 272 cycle-form LRAT certificates excluding E1279/13.

Lean proves completeness of a pruned chain-row enumeration, checks its
conjugations into these cycle forms, normalizes two more cells by the
centralizer of the first row, and checks every LRAT certificate. The CNF
includes the converse cancellation steps in both of its defining triangles.
Ordinary builds never invoke a solver. --solve reconstructs all certificates.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
from functools import cache
from itertools import product
import gzip
import json
from pathlib import Path
import subprocess
import time

from spectrum_small_pair_certificates import clauses, ROOT
from spectrum_63_ten_certificate import sha, TRIM

DATA = ROOT / "data/spectrum/1279_order13_refutations.json"
DEST = ROOT / "equational_theories/Spectrum/SmallPairs/OrderThirteen"


def partitions(n, lower=1):
    if n == 0:
        yield []
    for k in range(lower, n + 1):
        for tail in partitions(n - k, k):
            yield [k] + tail


def cycle_rows():
    result = []
    for first in range(1, 14):
        for rest in partitions(13 - first):
            row, offset = [], 0
            for length in [first] + rest:
                row += list(range(offset + 1, offset + length)) + [offset]
                offset += length
            result.append(([first] + rest, row))
    assert len(result) == 272
    return result


@cache
def base_clauses():
    cs = clauses(1279, 13)
    p = lambda x,y,z: 1 + (x*13+y)*13+z
    q = lambda x,y,z: 1 + 13**3 + (x*13+y)*13+z
    for x,y,a,b in product(range(13), repeat=4):
        cs.append([p(x,x,a), -p(a,y,b), -q(x,y,b)])
        cs.append([q(x,y,a), -p(a,y,b), -p(y,b,x)])
    return [c for c in cs if not any(-a in c for a in c)]


@cache
def base_cnf():
    return "".join(" ".join(map(str, c)) + " 0\n" for c in base_clauses()).encode()


def targets(cycles, locked):
    """Representatives for the centralizer fixing every point in locked."""
    offset, seen, result = 0, set(), []
    for length in cycles:
        block = list(range(offset, offset + length))
        offset += length
        if any(x in locked for x in block):
            result += block
        elif length not in seen:
            result.append(block[0])
            seen.add(length)
    return result


def case_clauses(i):
    cycles, row = cycle_rows()[i]
    p = lambda x,y,z: 1 + (x*13+y)*13+z
    cs = [[p(0,y,z)] for y,z in enumerate(row)]
    cs += [[-p(1,1,z)] for z in range(13) if z not in targets(cycles, [0,1])]
    cs += [[-p(1,1,z), -p(1,0,t)] for z,t in product(range(13), repeat=2)
        if t not in targets(cycles, [0,1,z])]
    return cs


def cnf(i):
    extra = case_clauses(i)
    return (f"p cnf {2 * 13**3} {len(base_clauses()) + len(extra)}\n".encode()
        + base_cnf() + "".join(" ".join(map(str, c)) + " 0\n" for c in extra).encode())


def moving_permutation(cycles, locked, z):
    blocks, offset = [], 0
    for length in cycles:
        blocks.append(list(range(offset, offset + length)))
        offset += length
    source = next(c for c in blocks if z in c)
    result = list(range(13))
    if any(x in locked for x in source):
        return result
    target = next(c for c in blocks if len(c) == len(source)
        and not any(x in locked for x in c))
    k = source.index(z)
    for a, b in zip(source[k:] + source[:k], target):
        result[a] = b
        if source != target:
            result[b] = a
    return result


def render_permutations(records):
    perms, ids, choices = [], {}, []
    for record in records:
        cycles = record["cycles"]
        for z,t in product(range(13), repeat=2):
            a = moving_permutation(cycles, [0,1], z)
            b = moving_permutation(cycles, [0,1,a[z]], a[t])
            p = tuple(b[a[x]] for x in range(13))
            if p not in ids:
                ids[p] = len(perms)
                perms.append(p)
            choices.append(ids[p])
    assert len(perms) == 1547
    inverse = [tuple(p.index(x) for x in range(13)) for p in perms]
    alphabet = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
    literal = lambda values: json.dumps("".join(alphabet[x] for x in values))
    first_allowed = [int(z in targets(r["cycles"], [0,1])) for r in records for z in range(13)]
    second_allowed = [int(t in targets(r["cycles"], [0,1,z])) for r in records
        for z,t in product(range(13), repeat=2)]
    text = '''import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.Basic

/-! Generated permutations witnessing the two further symmetry reductions.
The indices select only 1547 distinct permutations for the 45968 choices of
row and two entries. ASCII letters encode digits 0..51; a permutation entry
uses one digit and a choice index uses two. Constant-time byte access avoids
large nested array terms. Inverses and normalization are checked in Lean. -/
namespace Spectrum.SmallPairs.OrderThirteen

private def permValues : String := ''' + literal([x for p in perms for x in p]) + '''

private def inverseValues : String := ''' + literal([x for p in inverse for x in p]) + '''

private def digit (s : String) (j : ℕ) : ℕ :=
  if h : j < s.utf8ByteSize then
    let b := (s.getUTF8Byte ⟨j⟩ h).toNat
    if b < 97 then b - 65 else b - 71
  else 0

def permValue (i : Fin 1547) (x : Fin 13) : Fin 13 :=
  ⟨digit permValues (i.val*13+x.val) % 13, Nat.mod_lt _ (by decide)⟩

def inverseValue (i : Fin 1547) (x : Fin 13) : Fin 13 :=
  ⟨digit inverseValues (i.val*13+x.val) % 13, Nat.mod_lt _ (by decide)⟩

@[spectrum_native]
theorem inverse_checked : ∀ (i : Fin 1547) (x : Fin 13),
    inverseValue i (permValue i x) = x ∧ permValue i (inverseValue i x) = x := by
  native_decide

def savedPermutation (i : Fin 1547) : Equiv.Perm (Fin 13) where
  toFun := permValue i
  invFun := inverseValue i
  left_inv x := (inverse_checked i x).1
  right_inv x := (inverse_checked i x).2

private def choices : String := ''' + literal([d for x in choices for d in divmod(x,52)]) + '''

def reduction (i : Fin 272) (z t : Fin 13) : Equiv.Perm (Fin 13) :=
  let j := ((i.val*13+z.val)*13+t.val)*2
  savedPermutation ⟨(52 * digit choices j + digit choices (j+1)) % 1547,
    Nat.mod_lt _ (by decide)⟩

private def firstAllowedData : String := ''' + literal(first_allowed) + '''
private def secondAllowedData : String := ''' + literal(second_allowed) + '''

def firstAllowed (i : Fin 272) (z : Fin 13) : Bool :=
  digit firstAllowedData (i.val*13+z.val) == 1

def secondAllowed (i : Fin 272) (z t : Fin 13) : Bool :=
  digit secondAllowedData ((i.val*13+z.val)*13+t.val) == 1

private def rowData : String := ''' + literal([x for r in records for x in r["row"]]) + '''

def compactRow (i : Fin 272) (x : Fin 13) : Fin 13 :=
  ⟨digit rowData (i.val*13+x.val) % 13, Nat.mod_lt _ (by decide)⟩

end Spectrum.SmallPairs.OrderThirteen
'''
    (DEST / "Permutations.lean").write_text(text)


def render(records):
    DEST.mkdir(parents=True, exist_ok=True)
    render_permutations(records)
    rows = ["![" + ",".join(map(str, r["row"])) + "]" for r in records]
    text = (
        """import equational_theories.Spectrum.SmallPairs.ChainRows
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-! Generated canonical rows: the cycle containing zero comes first; the other
cycles have nondecreasing lengths. No assertion about unenumerated permutations
is trusted here: Canonical.lean checks all rows in the proved chain enumeration. -/
namespace Spectrum.SmallPairs.OrderThirteen

def row (i : Fin 272) : Fin 13 → Fin 13 :=
  #["""
        + ",\n    ".join(rows)
        + """][i.val]!

def rows : List (Fin 13 → Fin 13) := (List.finRange 272).map row

end Spectrum.SmallPairs.OrderThirteen
"""
    )
    (DEST / "Rows.lean").write_text(text)
    text = """import equational_theories.Spectrum.SmallPairs.OrderThirteen.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/-! Generated saved LRAT proofs. Hashes and solver timings are in
 data/spectrum/1279_order13_refutations.json. -/
namespace Spectrum.SmallPairs.OrderThirteen
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofTexts : Array String := #[
"""
    text += ",\n".join(
        '  -- Expanded LRAT SHA-256: ' + r['proof_sha256'] + '\n'
        + '  include_gzip_str "../../../../' + r['certificate'] + '"'
        for r in records
    )
    text += """]

/-- Parse one case at a time to bound the memory used by the finite check. -/
private def proof (i : Fin 272) : Array IntAction :=
  (parseLRATProof proofTexts[i.val]!.toUTF8).toOption.getD #[]

private def allChecked : Bool :=
  let common := natBase
  (List.finRange 272).all (fun i => check (proof i) (natFormulaWith common i))

@[spectrum_native]
private theorem all_checked : allChecked = true := by native_decide

theorem checked (i : Fin 272) : check (proof i) (natFormula i) = true := by
  exact List.all_eq_true.mp all_checked i (List.mem_finRange i)

theorem unsat (i : Fin 272) : (natFormula i).Unsat :=
  check_sound _ _ (checked i)

spectrum_assert unsat complete
end Spectrum.SmallPairs.OrderThirteen
"""
    (DEST / "Certificates.lean").write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solve", action="store_true")
    parser.add_argument("--reuse", type=Path, help="resume from saved raw proofs and search_seconds.json")
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    if min(args.timeout, args.jobs) < 1:
        parser.error("bounds must be positive")
    shapes = cycle_rows()
    if args.solve or args.reuse:
        cache = args.reuse or ROOT / ".cache/e1279-thirteen/optimized"
        cache.mkdir(parents=True, exist_ok=True)
        hashes = [sha(cnf(i)) for i in range(272)]
        hash_path = cache / "cnf_hashes.json"
        if args.reuse:
            if not hash_path.exists() or json.loads(hash_path.read_text()) != hashes:
                raise RuntimeError("Saved search uses a different encoding; rerun --solve")
        if args.solve:
            hash_path.write_text(json.dumps(hashes) + "\n")
            def run(item):
                i, (_, row) = item
                inp, proof = cache / f"{i}.cnf", cache / f"{i}.lrat"
                inp.write_bytes(cnf(i))
                start = time.monotonic()
                cp = subprocess.run(["cadical", "--quiet", "--shrink=0", "--lrat",
                    "--no-binary", "-t", str(args.timeout), str(inp), str(proof)],
                    capture_output=True, text=True)
                seconds = time.monotonic() - start
                if cp.returncode != 20:
                    raise RuntimeError(f"No refutation for row {i}: {cp.stdout}")
                inp.unlink()
                print(f"row {i:03}: {seconds:.3f}s", flush=True)
                return i, seconds
            with ThreadPoolExecutor(max_workers=args.jobs) as pool:
                timings = dict(pool.map(run, enumerate(shapes)))
            (cache / "search_seconds.json").write_text(json.dumps(timings) + "\n")
            archived = {}
        else:
            timings = {int(i):t for i,t in json.loads((cache / "search_seconds.json").read_text()).items()}
            saved = cache / "archived.json"
            archived = {r["index"]:r for r in json.loads(saved.read_text())} if saved.exists() else {}
        pending = [i for i in range(272) if i not in archived]
        trim_source = TRIM.replace(
            '    dumpLRATProof (file ++ ".trimmed") trimmed false',
            '    dumpLRATProof (file ++ ".trimmed") trimmed false\n    IO.FS.removeFile file')
        (cache / "Trim.lean").write_text(trim_source)
        pending_raw = [i for i in pending if (cache / f"{i}.lrat").exists()]
        if pending_raw:
            subprocess.run(["lake", "env", "lean", "--run", str(cache / "Trim.lean"),
                *(str(cache / f"{i}.lrat") for i in pending_raw)], cwd=ROOT, check=True)
        records = []
        for i, (cycles, row) in enumerate(shapes):
            if i in archived:
                r = archived[i]
                assert r["cnf_sha256"] == hashes[i], "Archived CNF changed: rerun --solve"
                zipped = (ROOT / r["certificate"]).read_bytes()
                assert sha(zipped) == r["compressed_sha256"]
                assert sha(gzip.decompress(zipped)) == r["proof_sha256"]
            else:
                rawpath = cache / f"{i}.lrat.trimmed"
                raw = rawpath.read_bytes()
                zipped = gzip.compress(raw, mtime=0)
                path = ROOT / f"data/spectrum/1279_thirteen_lrat/row{i:03}.lrat.gz"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(zipped)
                assert gzip.decompress(path.read_bytes()) == raw
                r = dict(index=i,certificate=str(path.relative_to(ROOT)),
                    proof_sha256=sha(raw),compressed_sha256=sha(zipped),
                    proof_bytes=len(raw),compressed_bytes=len(zipped))
                rawpath.unlink()
                (cache / f"{i}.lrat").unlink(missing_ok=True)
            r.update(index=i,row=row,cycles=cycles,search_seconds=round(timings[i],3),
                clauses=len(base_clauses()) + len(case_clauses(i)),
                cnf_sha256=sha(cnf(i)))
            records.append(r)
            archived[i] = r
            (cache / "archived.json").write_text(json.dumps(list(archived.values()),indent=2)+"\n")
        DATA.write_text(json.dumps(records,indent=2)+"\n")
    else:
        records = json.loads(DATA.read_text())
        assert len(records) == 272
        for (cycles,row),r in zip(shapes,records):
            assert (cycles,row) == (r["cycles"],r["row"])
            assert sha(cnf(r["index"])) == r["cnf_sha256"]
            zipped = (ROOT / r["certificate"]).read_bytes()
            assert sha(zipped) == r["compressed_sha256"]
            assert sha(gzip.decompress(zipped)) == r["proof_sha256"]
    render(records)
    print(f'Verified/rendered 272 cases, {sum(r["compressed_bytes"] for r in records):,} compressed bytes.')


if __name__ == "__main__":
    main()
