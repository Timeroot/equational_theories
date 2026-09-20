#!/usr/bin/env python3
"""Independently recount and reproduce the larger truncated-ring certificates."""
import argparse
from functools import lru_cache
import json
from pathlib import Path
from spectrum_generate import load_equations, variables
from definability_ring_counts_check import term, recount

ROOT = Path(__file__).resolve().parents[1]
E = load_equations()


def render(D):
    results = {}
    selected = [D["candidates"][i] for i in D["selected_indices"]]
    for index, (p, d) in enumerate(
        sorted({(e["modulus"], e["degree"]) for e in selected})
    ):
        batch = [e for e in selected if (e["modulus"], e["degree"]) == (p, d)]
        counts = {e[k]: e[k + "_count"] for e in batch for k in ["source", "target"]}
        ring = f"(Magma.TruncatedPolynomial.T (ZMod {p}) {d})"
        s = """import equational_theories.Definability.ScalarFamilyCounting
 import equational_theories.Definability.TruncatedPolynomialRing
 
 /-! Affine counts with cached multiplication kernels. -/
 open Law Law.MagmaLaw Magma.ScalarFamily Magma.AffineFamily
 set_option maxRecDepth 100000
 set_option maxHeartbeats 2000000
 
 """
        for law in sorted(counts):
            l, r = E[law - 1]
            k = 1 + max("xyzuvw".index(v) for v in variables(l) | variables(r))
            s += f"""private def law{law} : MagmaLaw (Fin {k}) := ⟨{term(l)}, {term(r)}⟩
 private theorem count{law} : count (R := {ring}) law{law} = {counts[law]} := by native_decide
 
 """
        for e in batch:
            a, t = e["source"], e["target"]
            k = 1 + max(
                "xyzuvw".index(v) for term0 in E[t - 1] for v in variables(term0)
            )
            name = f"Equation{t}_not_termStructuralFromFin_Equation{a}_largerTruncatedCount"
            s += f"""theorem {name} : ¬ Law{t}.TermStructuralFromFin Law{a} := by
   apply not_termStructuralFromFin_of_cloneFamily_count (op (R := {ring})) op_injective
     (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
     (Test law{a}) (Test law{t})
   · intro p hp φ
     exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
   · intro p hp
     apply (test_iff_satisfies _ _).mpr
     intro φ
     exact hp (fun i => φ (Fin.ofNat {k} i))
   · rw [card_test, card_test, count{a}, count{t}]
     decide
 
 #print axioms {name}
 
 """
        results[f"LargerTruncatedCount{index}.lean"] = s
    for filename, s in results.items():
        for name, axioms in D.get("axioms", {}).items():
            s = s.replace(
                "#print axioms " + name + "\n",
                "/-- info: "
                + axioms
                + " -/\n#guard_msgs (whitespace := lax) in\n#print axioms "
                + name
                + "\n",
            )
        results[filename] = (
            "\n".join(
                line[1:] if line.startswith(" ") else line for line in s.splitlines()
            )
            + "\n"
        )
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--render-only", action="store_true")
    args = parser.parse_args()
    D = json.loads(
        (ROOT / "data/definability_larger_truncated_counts.json").read_text()
    )

    @lru_cache(None)
    def count(law, p, d):
        return recount(E[law - 1], p, d, "affine", True)

    for e in [] if args.render_only else D["candidates"]:
        for key in ["source", "target"]:
            actual = count(e[key], e["modulus"], e["degree"])
            assert actual == e[key + "_count"], (e, key, actual)
    for filename, s in render(D).items():
        output = ROOT / "equational_theories/Definability/Generated" / filename
        if args.write:
            output.write_text(s)
        else:
            assert output.read_text() == s, f"Regenerate {output} with --write"
    print(
        (
            "Reproduced larger-ring Lean declarations."
            if args.render_only
            else f"Independently verified {len(D['candidates'])} larger-ring count obstructions."
        ),
        flush=True,
    )


if __name__ == "__main__":
    main()
