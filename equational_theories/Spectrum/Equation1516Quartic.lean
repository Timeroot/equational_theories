import equational_theories.Spectrum.Linear
import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Tactic.Ring

/-! E1516 models at every positive fourth-power order. In
`R[t]/(t⁴+2t³+2t²+t+1)`, put `x ◇ y = -(1+t+t²)x + ty`.
The proof expands four linear coordinates over an arbitrary commutative ring;
it does not enumerate multiplication tables or pairs of elements.

The earlier finite-field survey found an isomorphic model, but its existence
had not been included in the formal spectrum bounds. -/

namespace Spectrum.E1516
open Law Law.MagmaLaw

/-- Polynomial-basis coordinates, with `t⁴ = -2t³-2t²-t-1`. -/
def quarticOp {R : Type*} [CommRing R] (x y : R × R × R × R) : R × R × R × R :=
  (-x.1 + x.2.2.1 - x.2.2.2 - y.2.2.2,
   -x.1 - x.2.1 + x.2.2.1 + y.1 - y.2.2.2,
   -x.1 - x.2.1 + x.2.2.1 - x.2.2.2 + y.2.1 - 2*y.2.2.2,
   -x.2.1 + x.2.2.1 - x.2.2.2 + y.2.2.1 - 2*y.2.2.2)

theorem quartic_law {R : Type*} [CommRing R] :
    @Equation1516 (R × R × R × R) ⟨quarticOp⟩ := by
  intro x y
  change x = quarticOp (quarticOp y y) (quarticOp x (quarticOp x y))
  rcases x with ⟨x₀, x₁, x₂, x₃⟩
  rcases y with ⟨y₀, y₁, y₂, y₃⟩
  simp only [quarticOp, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

theorem model_fourthPower (n : ℕ) [NeZero n] : Law1516.HasModel (n^4) :=
  hasModel_of_card (⟨quarticOp⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law1516.models_iff _ ⟨quarticOp⟩).mpr quartic_law)
    (by simp [pow_succ, Nat.mul_assoc])

theorem model16 : Law1516.HasModel 16 :=
  model_fourthPower 2

theorem fourth_powers : fourthPowers ⊆ Law1516.spectrum := by
  rintro n ⟨hn, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  letI : NeZero k := ⟨hk⟩
  exact ⟨hn, model_fourthPower k⟩

spectrum_assert model_fourthPower complete
spectrum_assert model16 complete
spectrum_assert fourth_powers complete

/-- info: 'Spectrum.E1516.model16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model16

end Spectrum.E1516
