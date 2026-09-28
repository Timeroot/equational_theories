import equational_theories.Spectrum.Linear
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Tactic.Ring

/-! Small positive witnesses retained by the September open-spectrum survey.
The nine-element models use explicit two-coordinate operations on `ZMod 3`;
no multiplication table or finite-field extension implementation is needed.
The new prime-order models also retain their idempotent operations as design
seeds. Existing modular models and the uniform fourth-power constructions are
not duplicated here. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Spectrum.OpenWitnesses
open Law Law.MagmaLaw

/-- Multiplication by `1` and `1+i` on F₉, where `i²=-1`. -/
def op1516_9 {R : Type*} [CommRing R] (x y : R × R) : R × R :=
  (x.1 + y.1 - y.2, x.2 + y.1 + y.2)

/-- Multiplication by `-1+i` and `2-i` on F₉. -/
def op1286_9 {R : Type*} [CommRing R] (x y : R × R) : R × R :=
  (-x.1 - x.2 + 2*y.1 + y.2, x.1 - x.2 - y.1 + 2*y.2)

/-- Multiplication by `i` and `1-i` on F₉. -/
def op670_9 {R : Type*} [CommRing R] (x y : R × R) : R × R :=
  (-x.2 + y.1 + y.2, x.1 - y.1 + y.2)

theorem op1286_9_idempotent {R : Type*} [CommRing R] (x : R × R) :
    op1286_9 x x = x := by
  apply Prod.ext <;> simp only [op1286_9] <;> ring

theorem op670_9_idempotent {R : Type*} [CommRing R] (x : R × R) :
    op670_9 x x = x := by
  apply Prod.ext <;> simp only [op670_9] <;> ring

theorem law1516_9 : @Equation1516 (ZMod 3 × ZMod 3) ⟨op1516_9⟩ := by decide

theorem law1286_9 : @Equation1286 (ZMod 3 × ZMod 3) ⟨op1286_9⟩ := by decide

theorem law670_9 : @Equation670 (ZMod 3 × ZMod 3) ⟨op670_9⟩ := by decide

theorem model_1516_9 : Law1516.HasModel 9 :=
  hasModel_of_card (⟨op1516_9⟩ : Magma (ZMod 3 × ZMod 3))
    ((@Law1516.models_iff _ ⟨op1516_9⟩).mpr law1516_9) (by simp)

theorem model_1286_9 : Law1286.HasModel 9 :=
  hasModel_of_card (⟨op1286_9⟩ : Magma (ZMod 3 × ZMod 3))
    ((@Law1286.models_iff _ ⟨op1286_9⟩).mpr law1286_9) (by simp)

theorem model_670_9 : Law670.HasModel 9 :=
  hasModel_of_card (⟨op670_9⟩ : Magma (ZMod 3 × ZMod 3))
    ((@Law670.models_iff _ ⟨op670_9⟩).mpr law670_9) (by simp)

/-- The idempotent affine operation with first coefficient `a`. -/
def idempotentScalar {R : Type*} [CommRing R] (a : R) (x y : R) : R :=
  a*x+(1-a)*y

theorem idempotentScalar_self {R : Type*} [CommRing R] (a x : R) :
    idempotentScalar a x x = x := by
  unfold idempotentScalar
  ring

/-- Unlike the previously recorded order-eleven witness, this one is idempotent. -/
theorem law670_11_idempotent :
    @Equation670 (ZMod 11) ⟨idempotentScalar 6⟩ := by decide

theorem law1076_19 : @Equation1076 (ZMod 19) ⟨idempotentScalar 4⟩ := by decide

theorem law1313_19 : @Equation1313 (ZMod 19) ⟨idempotentScalar 16⟩ := by decide

theorem law907_23 : @Equation907 (ZMod 23) ⟨idempotentScalar 3⟩ := by decide

theorem model_1076_19 : Law1076.HasModel 19 :=
  hasModel_of_card (⟨idempotentScalar 4⟩ : Magma (ZMod 19))
    ((@Law1076.models_iff _ ⟨idempotentScalar 4⟩).mpr law1076_19) (ZMod.card 19)

theorem model_1313_19 : Law1313.HasModel 19 :=
  hasModel_of_card (⟨idempotentScalar 16⟩ : Magma (ZMod 19))
    ((@Law1313.models_iff _ ⟨idempotentScalar 16⟩).mpr law1313_19) (ZMod.card 19)

theorem model_907_23 : Law907.HasModel 23 :=
  hasModel_of_card (⟨idempotentScalar 3⟩ : Magma (ZMod 23))
    ((@Law907.models_iff _ ⟨idempotentScalar 3⟩).mpr law907_23) (ZMod.card 23)

spectrum_assert model_1516_9 complete
spectrum_assert model_1286_9 complete
spectrum_assert model_670_9 complete
spectrum_assert model_1076_19 complete
spectrum_assert model_1313_19 complete
spectrum_assert model_907_23 complete
spectrum_assert law670_11_idempotent complete

/-- info: 'Spectrum.OpenWitnesses.model_1516_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_1516_9
/-- info: 'Spectrum.OpenWitnesses.model_1286_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_1286_9
/-- info: 'Spectrum.OpenWitnesses.model_670_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_670_9
/-- info: 'Spectrum.OpenWitnesses.model_1076_19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_1076_19
/-- info: 'Spectrum.OpenWitnesses.model_1313_19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_1313_19
/-- info: 'Spectrum.OpenWitnesses.model_907_23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms model_907_23

end Spectrum.OpenWitnesses
