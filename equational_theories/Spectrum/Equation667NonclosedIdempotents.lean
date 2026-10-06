import equational_theories.Spectrum.Status
import equational_theories.Equations.Eqns1_999
import Mathlib.Data.Fin.VecNotation

/-! A retained structural counterexample, not a spectrum seed. The original
nine-element table is stored in `data/spectrum/667_883_research.json`, under
`square_endomorphism_counterexamples`. Its idempotents are not closed under
multiplication, so such closure is not a sound order-twelve search constraint. -/
namespace Spectrum.E667.NonclosedIdempotents

@[implicit_reducible]
def table : Magma (Fin 9) :=
  ⟨fun x y => ![![0, 3, 6, 7, 8, 1, 4, 2, 5],
    ![2, 6, 3, 8, 1, 5, 7, 0, 4],
    ![8, 7, 4, 1, 0, 2, 6, 5, 3],
    ![6, 2, 0, 5, 4, 8, 3, 1, 7],
    ![1, 4, 7, 3, 2, 0, 5, 8, 6],
    ![7, 1, 5, 0, 6, 3, 8, 4, 2],
    ![5, 8, 2, 6, 7, 4, 1, 3, 0],
    ![4, 5, 8, 2, 3, 6, 0, 7, 1],
    ![3, 0, 1, 4, 5, 7, 2, 6, 8]] x y⟩

local instance : Magma (Fin 9) := table

theorem law : Equation667 (Fin 9) := by decide +kernel

theorem idempotents (x : Fin 9) : x ◇ x = x ↔ x = 0 ∨ x = 7 ∨ x = 8 := by
  revert x
  decide +kernel

/-- Both inputs are idempotent, but their product is not. -/
theorem failure : (0 : Fin 9) ◇ 0 = 0 ∧ (7 : Fin 9) ◇ 7 = 7 ∧
    ((0 : Fin 9) ◇ 7) ◇ ((0 : Fin 9) ◇ 7) ≠ (0 : Fin 9) ◇ 7 := by
  decide +kernel

spectrum_assert law complete
spectrum_assert failure complete
end Spectrum.E667.NonclosedIdempotents
