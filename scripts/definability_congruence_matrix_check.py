#!/usr/bin/env python3
"""Check the diagonal-modulo-three matrix family and reproduce its certificates."""
import argparse
import itertools
import json
from pathlib import Path

import numpy as np

from definability_ring_counts_check import term
from spectrum_generate import load_equations, variables

ROOT = Path(__file__).resolve().parents[1]


def render(data):
    equations = load_equations()
    result = {}
    entry = data["candidates"][0]
    counts = {entry[key]: entry[key + "_count"] for key in ("source", "target")}
    for law, count in sorted(counts.items()):
        lhs, rhs = equations[law - 1]
        k = 1 + max("xyzuvw".index(v) for v in variables(lhs) | variables(rhs))
        result[
            f"CongruenceMatrixCount{law}.lean"
        ] = f"""import equational_theories.Definability.CongruenceMatrixFastTest

open Law Law.MagmaLaw Magma.CongruenceMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Magma.CongruenceMatrixCounts

def law{law} : MagmaLaw (Fin {k}) := ⟨{term(lhs)}, {term(rhs)}⟩
theorem count{law} : Fintype.card {{p : Params // Test law{law} p}} = {count} := by native_decide

end Magma.CongruenceMatrixCounts
"""
    text = """import equational_theories.Definability.Generated.CongruenceMatrixCount1045
import equational_theories.Definability.Generated.CongruenceMatrixCount1632

open Law Law.MagmaLaw Magma.CongruenceMatrix Magma.CongruenceMatrixCounts

theorem Equation1045_not_termStructuralFromFin_Equation1632_congruenceMatrix :
    ¬ Law1045.TermStructuralFromFin Law1632 := by
  apply not_termStructuralFromFin_of_cloneFamily_count operation operation_injective
    (one, zero) (zero, one) composition operation_fst operation_snd operation_comp
    (fun p : Params => Test law1632 p) (fun p : Params => Test law1045 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1632, count1045]
    decide

#print axioms Equation1045_not_termStructuralFromFin_Equation1632_congruenceMatrix
"""
    for name, axioms in data.get("axioms", {}).items():
        text = text.replace(
            f"#print axioms {name}\n",
            f"/-- info: {axioms} -/\n#guard_msgs (whitespace := lax) in\n#print axioms {name}\n",
        )
    result["CongruenceMatrixNegative.lean"] = text
    return result


def check(data):
    assert (data["modulus"], data["dimension"], data["kind"]) == (9, 2, "diagonal_mod3")
    parameters = list(itertools.product(range(9), range(9), range(3), range(3)))
    matrices = np.array([[[a, 3 * b], [3 * c, d]] for a, d, b, c in parameters])
    assert len(matrices) == data["matrix_count"] == 729
    assert len({tuple(a.flatten()) for a in matrices}) == 729
    assert data["parameters"] == len(matrices) ** 2 == 531441
    assert data["carrier_size"] == 81
    # Verify both the ring closure and the explicit coordinate operations used in Lean.
    a, d, b, c = np.array(parameters).T
    for first in range(0, len(matrices), 32):
        aa, dd, bb, cc = np.array(parameters[first : first + 32]).T
        expected_add = np.stack(
            [
                (aa[:, None] + a) % 9,
                3 * ((bb[:, None] + b) % 3),
                3 * ((cc[:, None] + c) % 3),
                (dd[:, None] + d) % 9,
            ],
            axis=-1,
        ).reshape(-1, 729, 2, 2)
        expected_mul = np.stack(
            [
                aa[:, None] * a % 9,
                3 * ((aa[:, None] * b + bb[:, None] * d) % 3),
                3 * ((cc[:, None] * a + dd[:, None] * c) % 3),
                dd[:, None] * d % 9,
            ],
            axis=-1,
        ).reshape(-1, 729, 2, 2)
        left = matrices[first : first + 32, None]
        right = matrices[None]
        assert np.array_equal(expected_add, (left + right) % 9)
        assert np.array_equal(expected_mul, np.matmul(left, right) % 9)
    equations = load_equations()
    entry = data["candidates"][0]
    for key in ("source", "target"):
        lhs, rhs = equations[entry[key] - 1]
        names = sorted(variables(lhs) | variables(rhs))
        answer = 0
        for first in range(0, 531441, 4096):
            codes = np.arange(first, min(first + 4096, 531441))
            left, right = matrices[codes % 729], matrices[codes // 729]
            good = np.ones(len(codes), dtype=bool)
            for marked, coordinate in itertools.product(names, range(2)):

                def evaluate(t):
                    if isinstance(t, str):
                        return np.broadcast_to(
                            (
                                np.eye(2, dtype=np.int64)[coordinate]
                                if t == marked
                                else np.zeros(2, dtype=np.int64)
                            ),
                            (len(codes), 2),
                        )
                    return (
                        np.einsum("nij,nj->ni", left, evaluate(t[0]))
                        + np.einsum("nij,nj->ni", right, evaluate(t[1]))
                    ) % 9

                good &= np.all(evaluate(lhs) == evaluate(rhs), axis=-1)
            answer += int(good.sum())
        assert answer == entry[key + "_count"], (key, answer)
    assert entry["source_count"] > entry["target_count"]
    print("Verified subring closure and counts 3564 > 3133 among 531441 operations.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    data = json.loads(
        (ROOT / "data/definability_congruence_matrix_counts.json").read_text()
    )
    check(data)
    for filename, text in render(data).items():
        path = ROOT / "equational_theories/Definability/Generated" / filename
        if args.write:
            path.write_text(text)
        else:
            assert path.read_text() == text, f"Regenerate {path} with --write"


if __name__ == "__main__":
    main()
