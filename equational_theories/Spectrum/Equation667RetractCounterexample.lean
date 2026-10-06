import equational_theories.Spectrum.Status
import equational_theories.Equations.Eqns1_999
import Mathlib.Data.Fin.VecNotation

/-! A structural counterexample, not an additional spectrum seed.
Even idempotent squaring need not be a homomorphism, and its image (the
idempotents) need not be closed. The square fibers here form a valid
five-element quotient; failure of the square map to be a homomorphism does
not imply that its fibers fail to be a congruence. -/
namespace Spectrum.E667.RetractCounterexample

@[implicit_reducible]
def table : Magma (Fin 10) :=
  ⟨fun x y => ![![0,2,3,4,1,6,7,8,5,9],
    ![2,1,4,0,6,7,9,3,8,5],
    ![3,7,5,8,0,2,1,9,4,6],
    ![7,0,1,3,5,8,6,2,9,4],
    ![8,6,0,5,4,9,2,7,3,1],
    ![6,4,2,1,9,5,8,0,7,3],
    ![4,9,8,6,2,1,3,5,0,7],
    ![1,3,9,2,7,0,5,4,6,8],
    ![5,8,7,9,3,4,0,6,1,2],
    ![9,5,6,7,8,3,4,1,2,0]] x y⟩

local instance : Magma (Fin 10) := table

theorem law : Equation667 (Fin 10) := by decide +kernel

theorem square_retraction (x : Fin 10) :
    (x ◇ x) ◇ (x ◇ x) = x ◇ x := by
  revert x
  decide +kernel

/-- Zero and one are idempotent, but their product is not. -/
theorem failure : (0 : Fin 10) ◇ 0 = 0 ∧ (1 : Fin 10) ◇ 1 = 1 ∧
    ((0 : Fin 10) ◇ 1) ◇ ((0 : Fin 10) ◇ 1) ≠ (0 : Fin 10) ◇ 1 := by
  decide +kernel

spectrum_assert law complete
spectrum_assert square_retraction complete
spectrum_assert failure complete
end Spectrum.E667.RetractCounterexample
