#!/usr/bin/env python3
"""Verify and reproduce the sixteen-element rectangular symmetry certificates."""
import argparse
import itertools
import json
import re
from pathlib import Path
import numpy as np
from definability_counting_upgrades_check import model_indices, preserves
from spectrum_generate import load_equations

ROOT = Path(__file__).resolve().parents[1]
vec = lambda xs: "![" + ", ".join(map(str, xs)) + "]"
nested = lambda rows: vec([vec(r) for r in rows])


def arr(xs):
    return "#[" + ", ".join(map(str, xs)) + "]"


def matrix(xs):
    return arr([arr(row) for row in xs])


def render(D):
    G = len(D["group"])
    F = len(D["forbidden"])
    s = f"""import equational_theories.Definability.ExactAut
    
    /-! A sixteen-element product action gives FO-structural obstructions.
    Generated finite transport data are checked in Lean; no graph-search fact is assumed. -/
    
    open Law Law.MagmaLaw
    set_option maxRecDepth 100000
    set_option maxHeartbeats 2000000
    
    namespace Magma.RectangularSymmetry
    
    def perms : Fin {G} → Fin 16 → Fin 16 := {nested(D['group'])}
    def inverses : Fin {G} → Fin 16 → Fin 16 := {nested(D['group_inverse'])}
    def perm (i : Fin {G}) : Equiv.Perm (Fin 16) :=
      Magma.permOf (perms i) (inverses i) (by revert i; decide)
    
    def rep : Fin 4 → Fin 16 × Fin 16 := {vec([f'({x}, {y})' for x,y in D['representatives']])}
    def tr : Fin 16 → Fin 16 → Fin 4 × Fin {G} := {nested([[f'({a}, {b})' for a,b in row] for row in D['transport']])}
    def stabilizers : Fin 4 → Fin 2 → Fin {G} := {nested(D['stabilizers'])}
    def values (a b : Fin 2) (c : Fin 4) : Fin 4 → Fin 16 :=
      ![0, ![0, 1] a, ![0, 4] b, ![0, 1, 4, 5] c]
    def family (a b : Fin 2) (c : Fin 4) : Magma (Fin 16) :=
      ⟨Magma.transport perms tr (values a b c)⟩
    
    theorem classification (N : Magma (Fin 16)) (h : ∀ i, N.IsEndo (perms i)) :
        ∃ a b : Fin 2, ∃ c : Fin 4, family a b c = N := by
    """
    for i, vals in enumerate(D["values"]):
        n = len(vals)
        s += f"""  obtain ⟨v{i}, hv{i}⟩ := Magma.exists_val_of_isEndo (idx := stabilizers {i})
        (a := (rep {i}).1) (b := (rep {i}).2) (val := ({vec(vals)} : Fin {n} → Fin 16)) h
        (by decide) (by decide)
    """
    s += """  refine ⟨v1, v2, v3, ?_⟩
      have hv : values v1 v2 v3 = fun i => N.op (rep i).1 (rep i).2 := by
        funext i
        fin_cases i
        · simpa using hv0
        · exact hv1
        · exact hv2
        · exact hv3
      have ht := Magma.op_eq_transport (rep := rep) (tr := tr) h (by decide)
      apply congrArg Magma.mk
      change Magma.transport perms tr (values v1 v2 v3) = N.op
      rw [hv, ← ht]
    
    """
    s += f"def forbidden : Fin 16 → Fin 16 := {vec(D['forbidden'][0])}\n"
    s += f"def forbiddenInv : Fin 16 → Fin 16 := {vec(D['forbidden_inverse'][0])}\n"
    s += """def forbiddenPerm : Equiv.Perm (Fin 16) :=
      Magma.permOf forbidden forbiddenInv (by decide)
    
    """
    s += f"def sourceTables : Fin {len(D['sources'])} → Fin 16 → Fin 16 → Fin 16 := {vec([nested(t) for t in D['sources']])}\n"
    s += """def source (i : Fin 3) : Magma (Fin 16) := ⟨sourceTables i⟩
    
    theorem source_endos : ∀ s i, (source s).IsEndo (perms i) := by decide
    theorem source_not_endo : ∀ s, ¬ (source s).IsEndo forbidden := by decide
    
    theorem refutes {L L' : NatMagmaLaw} (s : Fin 3)
        (hs : @satisfies _ (Fin 16) (source s) L')
        (ht : ∀ a b c, @satisfies _ (Fin 16) (family a b c) L →
          (family a b c).IsEndo forbidden) :
        ¬ L.StructuralFromFin L' := by
      intro h
      obtain ⟨N, hN, hf, hb⟩ := h (source s) hs
      have he : ∀ i, N.IsEndo (perms i) := fun i =>
        Magma.IsEndo.of_definable (e := perm i) hf (source_endos s i)
      obtain ⟨a, b, c, rfl⟩ := classification N he
      exact source_not_endo s
        (Magma.IsEndo.of_definable (e := forbiddenPerm) hb (ht a b c hN))
    
    end Magma.RectangularSymmetry
    
    /-- info: 'Magma.RectangularSymmetry.refutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
    #guard_msgs (whitespace := lax) in
    #print axioms Magma.RectangularSymmetry.refutes
    """
    core = s
    s = """import equational_theories.Definability.RectangularSymmetry
    
    /-! Generated from data/definability_rectangular_symmetry.json. -/
    open Law Law.MagmaLaw Magma.RectangularSymmetry
    set_option maxRecDepth 100000
    set_option maxHeartbeats 2000000
    
    """
    for target in [3259, 3511]:
        s += f"""private theorem target{target} : ∀ a b c,
        @Equation{target} (Fin 16) (family a b c) → (family a b c).IsEndo forbidden := by decide
    
    """
    for i in D["selected_indices"]:
        e = D["candidates"][i]
        a, b, w = e["source"], e["target"], e["witness"]
        name = f"Equation{b}_not_structuralFromFin_Equation{a}_rectangularSymmetry"
        s += f"""theorem {name} : ¬ Law{b}.StructuralFromFin Law{a} := by
      apply refutes {w}
      · exact (@Law{a}.models_iff (Fin 16) (source {w})).mpr (by decide)
      · intro a b c h
        exact target{b} a b c ((@Law{b}.models_iff (Fin 16) (family a b c)).mp h)
    
    /-- info: '{name}' depends on axioms: [propext, Classical.choice, Quot.sound] -/
    #guard_msgs (whitespace := lax) in
    #print axioms {name}
    
    """
    proofs = s
    core = (
        "\n".join(
            line[4:] if line.startswith("    ") else line for line in core.splitlines()
        )
        + "\n"
    )
    proofs = (
        "\n".join(
            line[4:] if line.startswith("    ") else line
            for line in proofs.splitlines()
        )
        + "\n"
    )
    for key, name in [("group", "perms"), ("group_inverse", "inverses")]:
        replacement = f"def {name}Data : Array (Array (Fin 16)) := {matrix(D[key])}\ndef {name} (i : Fin 148) (x : Fin 16) : Fin 16 := ({name}Data.getD i.val #[]).getD x.val 0"
        core = re.sub(
            r"^def " + name + r" : .*$", lambda m: replacement, core, flags=re.M
        )
    replacement = f'def trData : Array (Array (Fin 4 × Fin 148)) := {matrix([[f"({a}, {b})" for a,b in row] for row in D["transport"]])}\ndef tr (x y : Fin 16) : Fin 4 × Fin 148 := (trData.getD x.val #[]).getD y.val (0, 0)'
    core = re.sub(r"^def tr : .*$", lambda m: replacement, core, flags=re.M)
    replacement = f'def sourceData : Array (Array (Array (Fin 16))) := {arr([matrix(t) for t in D["sources"]])}\ndef sourceTables (i : Fin 3) (x y : Fin 16) : Fin 16 := ((sourceData.getD i.val #[]).getD x.val #[]).getD y.val 0'
    core = re.sub(r"^def sourceTables : .*$", lambda m: replacement, core, flags=re.M)
    core = core.replace("def family (", "@[implicit_reducible] def family (").replace(
        "def source (", "@[implicit_reducible] def source ("
    )

    def finish(text):
        text = text.replace("decide", "native_decide")
        text = re.sub(
            r"/-- info:.*?-/\n#guard_msgs \(whitespace := lax\) in\n",
            "",
            text,
            flags=re.S,
        )
        for name, axioms in D.get("axioms", {}).items():
            text = text.replace(
                "#print axioms " + name + "\n",
                "/-- info: "
                + axioms
                + " -/\n#guard_msgs (whitespace := lax) in\n#print axioms "
                + name
                + "\n",
            )
        return text

    return finish(core), finish(proofs)


def check(d):
    group = np.array(d["group"])
    inverse = np.array(d["group_inverse"])
    identity = np.arange(16)
    for perm, inv in zip(group, inverse, strict=True):
        assert np.array_equal(inv[perm], identity) and np.array_equal(
            perm[inv], identity
        )
    for x, y in itertools.product(range(16), repeat=2):
        o, w = d["transport"][x][y]
        a, b = d["representatives"][o]
        assert group[w, a] == x and group[w, b] == y
    for i, (a, b) in enumerate(d["representatives"]):
        stabilizers = group[d["stabilizers"][i]]
        assert np.all(stabilizers[:, a] == a) and np.all(stabilizers[:, b] == b)
        assert (
            list(np.flatnonzero(np.all(stabilizers == identity, axis=0)))
            == d["values"][i]
        )
    tables = np.array(d["family"], dtype=np.uint8)
    sources = np.array(d["sources"], dtype=np.uint8)
    reconstructed = np.array(
        [
            [[group[w, values[o]] for o, w in row] for row in d["transport"]]
            for values in itertools.product(*d["values"])
        ]
    )
    assert {t.tobytes() for t in tables} == {
        t.astype(np.uint8).tobytes() for t in reconstructed
    }
    probe = np.array(d["forbidden"][0])
    inv = np.array(d["forbidden_inverse"][0])
    assert np.array_equal(inv[probe], identity)
    for source in sources:
        assert preserves(source, group) and not preserves(source, [probe])
    equations = load_equations()
    for e in d["candidates"]:
        assert (
            len(model_indices(equations, sources[e["witness"]][None], e["source"])) == 1
        )
    for target in {e["target"] for e in d["candidates"]}:
        assert all(
            preserves(tables[i], [probe])
            for i in model_indices(equations, tables, target)
        )
    assert {j for _, covered in d["coverage"] for j in covered} == set(
        range(len(d["candidates"]))
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = json.loads(
        (ROOT / "data/definability_rectangular_symmetry.json").read_text()
    )
    check(data)
    for relative, text in zip(
        [
            "Definability/RectangularSymmetry.lean",
            "Definability/Generated/RectangularSymmetry.lean",
        ],
        render(data),
        strict=True,
    ):
        output = ROOT / "equational_theories" / relative
        if args.write:
            output.write_text(text)
        else:
            assert output.read_text() == text, f"Regenerate {output} with --write"
    print("Verified 47 rectangular symmetry obstructions and reproduced eight proofs.")


if __name__ == "__main__":
    main()
