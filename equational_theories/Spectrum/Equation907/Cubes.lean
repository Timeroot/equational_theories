import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination

/-! E907 at every odd cube. The rank-three algebra used for its division-image
obstruction also gives a small explicit construction over any commutative ring
in which 2 has an inverse. Only three polynomial identities are checked.

In the basis `1,Q,Q²`, with `Q³=2Q-2`, division is `D(x,y)=(1-Q)x+Qy`.
The operation below is `Q⁻¹(y-(1-Q)x)`. It requires neither a field nor a
prime-power modulus. -/

namespace Spectrum.E907.Cubes
open Law Law.MagmaLaw

def op {R : Type*} [CommRing R] (h : R) (x y : Fin 3 → R) : Fin 3 → R :=
  ![y 0 + y 1 - x 1, x 1 + y 2 - x 2, x 2 + h * (x 0 - y 0)]

theorem op_self {R : Type*} [CommRing R] (h : R) (x : Fin 3 → R) :
    op h x x = x := by
  ext i
  fin_cases i <;> simp [op]

theorem law {R : Type*} [CommRing R] (h : R) (hh : 2 * h = 1) :
    @Equation907 (Fin 3 → R) ⟨op h⟩ := by
  intro x y
  change x = op h y (op h (op h y x) (op h x y))
  ext i
  fin_cases i <;> simp [op]
  · linear_combination (y 0 - x 0) * hh
  · linear_combination (y 1 - x 1) * hh
  · linear_combination (y 2 - x 2) * hh

theorem model_odd_cube (n : ℕ) (hn : Odd n) : Law907.HasModel (n ^ 3) := by
  obtain ⟨k, rfl⟩ := hn
  letI : NeZero (2 * k + 1) := ⟨by omega⟩
  have hh : (2 : ZMod (2 * k + 1)) * (k + 1) = 1 := by
    have hz := ZMod.natCast_self (2 * k + 1)
    push_cast at hz
    linear_combination hz
  let h : ZMod (2 * k + 1) := k + 1
  exact hasModel_of_card (⟨op h⟩ : Magma (Fin 3 → ZMod (2 * k + 1)))
    ((@Law907.models_iff _ ⟨op h⟩).mpr (law h hh)) (by simp)

theorem odd_cubes : oddCubes ⊆ Law907.spectrum := by
  rintro n ⟨hn, k, hk, rfl⟩
  exact ⟨hn, model_odd_cube k hk⟩

theorem model125 : Law907.HasModel 125 :=
  model_odd_cube 5 (by decide)

spectrum_assert model_odd_cube complete
spectrum_assert odd_cubes complete
spectrum_assert model125 complete

/-- info: 'Spectrum.E907.Cubes.model_odd_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_odd_cube

end Spectrum.E907.Cubes
