#!/usr/bin/env python3
"""Reproduce finite unary-endomorphism counts and their Lean coverage certificates.

The Python enumerator only supplies candidate lists. Lean checks source models,
injectivity, and complete target coverage independently. --scan surveys one
representative of every nonconstant, nonbijective unary map on 4 and 5 points,
skipping families above the stated bound; it does not alter the saved claims.
"""
import argparse
import itertools
import json
from pathlib import Path
import numpy as np
from spectrum_generate import load_equations, variables
from definability_counting_upgrades_check import model_indices

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data/definability_unary_tail_counts.json"
OUTPUT = ROOT / "equational_theories/Definability/Generated"
E = load_equations()
mi = model_indices


def commuting_tables(u, limit=150000):
    n = len(u)
    q = n * n
    parent = [u[x] * n + u[y] for x in range(n) for y in range(n)]
    # Break into cycles followed by vertices ordered from roots toward leaves.
    cycles = []
    seen = set()
    for v in range(q):
        path = []
        while v not in seen and v not in path:
            path.append(v)
            v = parent[v]
        if v in path:
            cycles.append(path[path.index(v) :])
        seen.update(path)
    assigned = set(v for c in cycles for v in c)
    order = []
    while len(assigned) < q:
        vs = [v for v in range(q) if v not in assigned and parent[v] in assigned]
        assert vs
        order.extend(vs)
        assigned.update(vs)
    arr = np.zeros((1, q), dtype=np.uint8)
    for c in cycles:
        choices = []
        for a in range(n):
            vals = [a]
            for _ in c[1:]:
                vals.append(u[vals[-1]])
            if u[vals[-1]] == a:
                choices.append(vals)
        if len(arr) * len(choices) > limit:
            return None
        arr = np.repeat(arr, len(choices), axis=0)
        arr[:, c] = np.tile(choices, (len(arr) // len(choices), 1))
    for v in order:
        p = arr[:, parent[v]]
        counts = np.array([sum(x == a for x in u) for a in p])
        if int(counts.sum()) > limit:
            return None
        idx = np.repeat(np.arange(len(arr)), counts)
        arr = arr[idx]
        pre = [np.flatnonzero(np.array(u) == a).tolist() for a in range(n)]
        arr[:, v] = [x for a in p for x in pre[a]]
    return arr.reshape(-1, n, n)


def can(u):
    n = len(u)
    best = u
    for p in itertools.permutations(range(n)):
        inv = [p.index(i) for i in range(n)]
        v = tuple(p[u[inv[i]]] for i in range(n))
        if v < best:
            return False
    return True


def render_four(u, ds):
    tables = commuting_tables(u)
    name = "UnaryTail" + "".join(map(str, u))
    s = (
        """import equational_theories.Definability.FourPointTable

/-! Generated finite endomorphism obstruction. Small source lists are checked
in the kernel; bv_decide verifies that the target lists are exhaustive. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FourPointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Magma."""
        + name
        + "\n\n"
    )
    s += (
        "def step (x : Point) : Point := "
        + "".join(f"if x = {i} then {v} else " for i, v in enumerate(u[:-1]))
        + str(u[-1])
        + "\n\n"
    )
    s += (
        "def endoTest (c : Code) : Prop :=\n  "
        + " ∧\n  ".join(
            f"decode c (step {x}) (step {y}) = step (decode c {x} {y})"
            for x in range(4)
            for y in range(4)
        )
        + "\n\n"
    )
    s += (
        "theorem endoTest_encode (f : Point → Point → Point) (h : Commutes step f) :\n    endoTest (encode f) := by\n  unfold endoTest\n  simp only [decode_encode]\n  exact ⟨"
        + ", ".join(f"h {x} {y}" for x in range(4) for y in range(4))
        + "⟩\n\n"
    )
    codes = {}
    for law in sorted({d[k] for d in ds for k in ["source", "target"]}):
        tab = tables[mi(E, tables, law)]
        codes[law] = [sum(int(a) << (2 * i) for i, a in enumerate(t.flat)) for t in tab]
        s += (
            f"def codes{law} : Fin {len(tab)} → Code := !["
            + ", ".join(map(str, codes[law]))
            + "]\n\n"
        )
    for law in sorted({d["source"] for d in ds}):
        s += f"""theorem source{law}_injective : Function.Injective (fun i => decode (codes{law} i)) := by
  intro i j h
  have hc := decode_injective h
  have hi : Function.Injective codes{law} := by decide +kernel
  exact hi hc

theorem source{law}_law : ∀ i, @Equation{law} Point ⟨decode (codes{law} i)⟩ := by
  decide +kernel

theorem source{law}_endo : ∀ i, Commutes step (decode (codes{law} i)) := by
  decide +kernel

"""
    for law in sorted({d["target"] for d in ds}):
        lhs, rhs = E[law - 1]
        from spectrum_generate import variables

        vs = sorted(variables(lhs) | variables(rhs))
        assigns = list(itertools.product(range(4), repeat=len(vs)))

        def term(t, env):
            return (
                str(env[t])
                if isinstance(t, str)
                else f"(decode c {term(t[0],env)} {term(t[1],env)})"
            )

        tests = [
            f"{term(lhs,dict(zip(vs,a)))} = {term(rhs,dict(zip(vs,a)))}"
            for a in assigns
        ]
        s += f"def test{law} (c : Code) : Prop :=\n  " + " ∧\n  ".join(tests) + "\n\n"
        s += (
            f"""theorem test{law}_encode (f : Point → Point → Point) (h : @Equation{law} Point ⟨f⟩) :
    test{law} (encode f) := by
  unfold test{law}
  simp only [decode_encode]
  exact ⟨"""
            + ", ".join("h " + " ".join(map(str, a)) for a in assigns)
            + "⟩\n\n"
        )
        n = len(codes[law])
        s += f"""theorem cover{law}_bits (c : Code) (he : endoTest c) (h : test{law} c) :
    ∃ i, codes{law} i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero, codes{law}, Fin.cons_zero,
    Fin.cons_succ]
  change {' ∨ '.join(str(v)+' = c' for v in codes[law])} ∨ False
  unfold endoTest test{law} decode step at *
  bv_decide (config := {{ timeout := 60 }})

theorem cover{law} (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation{law} Point ⟨f⟩) : ∃ i, decode (codes{law} i) = f := by
  obtain ⟨i, hi⟩ := cover{law}_bits (encode f) (endoTest_encode f he) (test{law}_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

"""
    s += "end Magma." + name + "\n\nopen Magma." + name + "\n\n"
    for d in ds:
        a, b = d["source"], d["target"]
        name0 = f"Equation{b}_not_termStructuralFromFin_Equation{a}_unaryTail"
        s += f"""theorem {name0} : ¬ Law{b}.TermStructuralFromFin Law{a} := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes{a} i))
    (fun i => decode (codes{b} i)) source{a}_injective
  · intro i
    exact (@Law{a}.models_iff Point ⟨decode (codes{a} i)⟩).mpr (source{a}_law i)
  · exact source{a}_endo
  · intro f he h
    exact cover{b} f he ((@Law{b}.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: '{name0}' depends on axioms: [propext, Classical.choice, Quot.sound,\ncover{b}_bits._native.bv_decide.ax_1_8] -/
#guard_msgs (whitespace := lax) in
#print axioms {name0}

"""
    return s


def render_five(u, ds):
    tables = commuting_tables(u)
    name = "UnaryTail" + "".join(map(str, u))
    s = (
        """import equational_theories.Definability.FivePointTable

/-! Generated finite endomorphism obstruction. Source tables are checked in
Lean's kernel; target-list completeness uses the standard bv_decide checker. -/
open Law Law.MagmaLaw Magma.UnaryMap Magma.FivePointTable
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Magma."""
        + name
        + "\n\n"
    )
    s += "def step (x : Point) : Point := ![" + ", ".join(map(str, u)) + "] x\n"
    s += (
        "def stepBits (x : BitVec 3) : BitVec 3 := "
        + "".join(f"if x = {i} then {v} else " for i, v in enumerate(u[:-1]))
        + str(u[-1])
        + "\n\n"
    )
    s += "theorem step_point (x : Point) : stepBits (point x) = point (step x) := by\n  fin_cases x <;> rfl\n\n"
    s += (
        "def endoTest (c : Code) : Prop :=\n  "
        + " ∧\n  ".join(
            f"bits c (stepBits {x}) (stepBits {y}) = stepBits (bits c {x} {y})"
            for x in range(5)
            for y in range(5)
        )
        + "\n\n"
    )
    s += (
        """theorem endoTest_encode (f : Point → Point → Point) (h : Commutes step f) :
    endoTest (encode f) := by
  have hh (x y : Point) : bits (encode f) (stepBits (point x)) (stepBits (point y)) =
      stepBits (bits (encode f) (point x) (point y)) := by
    rw [step_point, step_point, bits_encode, bits_encode, step_point]
    exact congrArg point (h x y)
  exact ⟨"""
        + ", ".join(f"hh {x} {y}" for x in range(5) for y in range(5))
        + "⟩\n\n"
    )
    codes = {}
    for law in sorted({d[k] for d in ds for k in ["source", "target"]}):
        tab = tables[mi(E, tables, law)]
        codes[law] = [sum(int(a) << (3 * i) for i, a in enumerate(t.flat)) for t in tab]
        s += (
            f"def codes{law} : Fin {len(tab)} → Code := !["
            + ", ".join(map(str, codes[law]))
            + "]\n\n"
        )
    for law in sorted({d["source"] for d in ds}):
        s += f"""theorem source{law}_injective : Function.Injective (fun i => decode (codes{law} i)) := by
  decide +kernel

theorem source{law}_law : ∀ i, @Equation{law} Point ⟨decode (codes{law} i)⟩ := by
  decide +kernel

theorem source{law}_endo : ∀ i, Commutes step (decode (codes{law} i)) := by
  decide +kernel

"""
    for law in sorted({d["target"] for d in ds}):
        lhs, rhs = E[law - 1]
        vs = sorted(variables(lhs) | variables(rhs))
        assigns = list(itertools.product(range(5), repeat=len(vs)))

        def term(t, env, c="c"):
            return (
                str(env[t])
                if isinstance(t, str)
                else f"(bits {c} {term(t[0],env,c)} {term(t[1],env,c)})"
            )

        tests = [
            f"{term(lhs,dict(zip(vs,a)))} = {term(rhs,dict(zip(vs,a)))}"
            for a in assigns
        ]
        s += f"def test{law} (c : Code) : Prop :=\n  " + " ∧\n  ".join(tests) + "\n\n"
        s += (
            f"""theorem test{law}_encode (f : Point → Point → Point) (h : @Equation{law} Point ⟨f⟩) :
    test{law} (encode f) := by
  have hh ({' '.join(vs)} : Point) :
    {term(lhs,{v:f'(point {v})' for v in vs},'(encode f)')} = {term(rhs,{v:f'(point {v})' for v in vs},'(encode f)')} := by
    simp only [bits_encode]
    exact congrArg point (h {' '.join(vs)})
  exact ⟨"""
            + ", ".join("hh " + " ".join(map(str, a)) for a in assigns)
            + "⟩\n\n"
        )
        s += f"""theorem cover{law}_bits (c : Code) (hv : Valid c) (he : endoTest c) (h : test{law} c) :
    ∃ i, codes{law} i = c := by
  simp only [Fin.exists_fin_succ, Fin.exists_fin_zero]
  change {' ∨ '.join(str(v)+' = c' for v in codes[law])} ∨ False
  unfold Valid endoTest test{law} bits stepBits at *
  bv_decide (config := {{ timeout := 60 }})

theorem cover{law} (f : Point → Point → Point) (he : Commutes step f)
    (h : @Equation{law} Point ⟨f⟩) : ∃ i, decode (codes{law} i) = f := by
  obtain ⟨i, hi⟩ := cover{law}_bits (encode f) (valid_encode f)
    (endoTest_encode f he) (test{law}_encode f h)
  exact ⟨i, (congrArg decode hi).trans (decode_encode f)⟩

"""
    s += "end Magma." + name + "\n\nopen Magma." + name + "\n\n"
    for d in ds:
        a, b = d["source"], d["target"]
        name0 = f"Equation{b}_not_termStructuralFromFin_Equation{a}_unaryTail"
        s += f"""theorem {name0} : ¬ Law{b}.TermStructuralFromFin Law{a} := by
  apply not_termStructuralFromFin_of_cover step (fun i => decode (codes{a} i))
    (fun i => decode (codes{b} i)) source{a}_injective
  · intro i
    exact (@Law{a}.models_iff Point ⟨decode (codes{a} i)⟩).mpr (source{a}_law i)
  · exact source{a}_endo
  · intro f he h
    exact cover{b} f he ((@Law{b}.models_iff Point ⟨f⟩).mp h)
  · decide

/-- info: '{name0}' depends on axioms: [propext, Classical.choice, Quot.sound,\ncover{b}_bits._native.bv_decide.ax_1_7] -/
#guard_msgs (whitespace := lax) in
#print axioms {name0}

"""
    return s


def verify(write=False):
    data = json.loads(DATA.read_text())
    for u in sorted({tuple(d["map"]) for d in data["candidates"]}):
        batch = [d for d in data["candidates"] if tuple(d["map"]) == u]
        family = commuting_tables(u)
        assert family is not None
        assert len(np.unique(family.reshape(len(family), -1), axis=0)) == len(family)
        unary = np.array(u, dtype=np.uint8)
        assert np.all(family[:, unary[:, None], unary[None, :]] == unary[family])
        counts = {
            a: len(model_indices(E, family, a))
            for a in {d[k] for d in batch for k in ["source", "target"]}
        }
        for d in batch:
            assert len(family) == d["family_count"]
            assert counts[d["source"]] == d["source_count"]
            assert counts[d["target"]] == d["target_count"]
            assert d["target_count"] < d["source_count"]
        proved = [d for d in batch if d["status"] == "lean"]
        if proved:
            rendered = (render_four if len(u) == 4 else render_five)(u, proved)
            path = OUTPUT / ("UnaryTail" + "".join(map(str, u)) + ".lean")
            if write:
                path.write_text(rendered)
            else:
                assert path.read_text() == rendered, f"Regenerate {path} with --write"
        print(
            f"{u}: {len(family):,} operations; {len(proved)} Lean arrows, "
            f"{len(batch)-len(proved)} research candidates",
            flush=True,
        )
    print("Counts and generated Lean sources agree.")


def scan(output, limit):
    snapshot = json.loads((ROOT / "docs/definability_open/snapshot.json").read_text())
    pairs = sorted(
        {
            (int(a), b)
            for a, row in snapshot["boards"]["termStructural/fin"]["open_rows"].items()
            for bs in row.values()
            for b in bs
        }
    )
    ids = sorted({x for ab in pairs for x in ab})
    index = {a: i for i, a in enumerate(ids)}
    ai = np.array([index[a] for a, b in pairs])
    bi = np.array([index[b] for a, b in pairs])
    result = dict(
        baseline_fingerprint=snapshot["fingerprint"],
        limit=limit,
        completed=[],
        skipped=[],
        candidates=[],
    )
    for n in [4, 5]:
        for u in itertools.product(range(n), repeat=n):
            if len(set(u)) in [1, n] or not can(u):
                continue
            family = commuting_tables(u, limit)
            if family is None:
                result["skipped"].append(u)
            else:
                counts = np.array([len(model_indices(E, family, a)) for a in ids])
                result["completed"].append(dict(map=u, family_count=len(family)))
                found = []
                for j in np.flatnonzero(counts[ai] > counts[bi]):
                    a, b = pairs[j]
                    found.append(
                        dict(
                            source=a,
                            target=b,
                            source_count=int(counts[index[a]]),
                            target_count=int(counts[index[b]]),
                            map=u,
                            family_count=len(family),
                            status="research",
                        )
                    )
                result["candidates"].extend(found)
                print(
                    u,
                    len(family),
                    [(d["source"], d["target"]) for d in found],
                    flush=True,
                )
            output.write_text(json.dumps(result, indent=2) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--write", action="store_true", help="regenerate the saved Lean modules"
    )
    ap.add_argument(
        "--scan", type=Path, help="write a new research survey to this path"
    )
    ap.add_argument("--limit", type=int, default=150000)
    args = ap.parse_args()
    if args.scan:
        scan(args.scan, args.limit)
    else:
        verify(args.write)


if __name__ == "__main__":
    main()
