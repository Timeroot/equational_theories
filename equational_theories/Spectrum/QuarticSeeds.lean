import equational_theories.Spectrum.Linear
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Explicit idempotent models at every positive fourth-power order for
E670, E677, E1076, E1083, E1286, and E1313. The operations are companion
matrix constructions over arbitrary commutative rings; proofs expand the
identities directly. See `docs/open_spectra_survey_20260927.md`. -/

namespace Spectrum.QuarticSeeds
open Law Law.MagmaLaw

def op {R : Type*} [CommRing R] (c0 c1 c2 c3 : R)
    (x y : R × R × R × R) : R × R × R × R :=
  (x.1 + c0 * (x.2.2.2 - y.2.2.2),
   x.2.1 - x.1 + y.1 + c1 * (x.2.2.2 - y.2.2.2),
   x.2.2.1 - x.2.1 + y.2.1 + c2 * (x.2.2.2 - y.2.2.2),
   x.2.2.2 - x.2.2.1 + y.2.2.1 + c3 * (x.2.2.2 - y.2.2.2))

theorem idempotent {R : Type*} [CommRing R] (c0 c1 c2 c3 : R) (x : R × R × R × R) :
    op c0 c1 c2 c3 x x = x := by
  ext <;> simp [op]

theorem law_670 {R : Type*} [CommRing R] :
    @Equation670 (R × R × R × R) ⟨op (-1) 1 0 (-2)⟩ := by
  intro x y
  ext <;> simp only [Magma.op, op] <;> ring

theorem model_670 (n : ℕ) [NeZero n] : Law670.HasModel (n^4) := by
  exact hasModel_of_card (⟨op (-1) 1 0 (-2)⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law670.models_iff _ ⟨op (-1) 1 0 (-2)⟩).mpr law_670) (by simp [pow_succ, Nat.mul_assoc])

spectrum_assert model_670 complete

theorem law_677 {R : Type*} [CommRing R] :
    @Equation677 (R × R × R × R) ⟨op 1 (-1) 1 (-1)⟩ := by
  intro x y
  ext <;> simp only [Magma.op, op] <;> ring

theorem model_677 (n : ℕ) [NeZero n] : Law677.HasModel (n^4) := by
  exact hasModel_of_card (⟨op 1 (-1) 1 (-1)⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law677.models_iff _ ⟨op 1 (-1) 1 (-1)⟩).mpr law_677) (by simp [pow_succ, Nat.mul_assoc])

spectrum_assert model_677 complete

theorem law_1076 {R : Type*} [CommRing R] :
    @Equation1076 (R × R × R × R) ⟨op (-1) 1 (-1) (-1)⟩ := by
  intro x y
  ext <;> simp only [Magma.op, op] <;> ring

theorem model_1076 (n : ℕ) [NeZero n] : Law1076.HasModel (n^4) := by
  exact hasModel_of_card (⟨op (-1) 1 (-1) (-1)⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law1076.models_iff _ ⟨op (-1) 1 (-1) (-1)⟩).mpr law_1076) (by simp [pow_succ, Nat.mul_assoc])

spectrum_assert model_1076 complete

theorem law_1083 {R : Type*} [CommRing R] :
    @Equation1083 (R × R × R × R) ⟨op 1 (-1) 2 (-2)⟩ := by
  intro x y
  ext <;> simp only [Magma.op, op] <;> ring

theorem model_1083 (n : ℕ) [NeZero n] : Law1083.HasModel (n^4) := by
  exact hasModel_of_card (⟨op 1 (-1) 2 (-2)⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law1083.models_iff _ ⟨op 1 (-1) 2 (-2)⟩).mpr law_1083) (by simp [pow_succ, Nat.mul_assoc])

spectrum_assert model_1083 complete

theorem law_1286 {R : Type*} [CommRing R] :
    @Equation1286 (R × R × R × R) ⟨op 1 (-1) 2 (-2)⟩ := by
  intro x y
  ext <;> simp only [Magma.op, op] <;> ring

theorem model_1286 (n : ℕ) [NeZero n] : Law1286.HasModel (n^4) := by
  exact hasModel_of_card (⟨op 1 (-1) 2 (-2)⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law1286.models_iff _ ⟨op 1 (-1) 2 (-2)⟩).mpr law_1286) (by simp [pow_succ, Nat.mul_assoc])

spectrum_assert model_1286 complete

theorem law_1313 {R : Type*} [CommRing R] :
    @Equation1313 (R × R × R × R) ⟨op (-1) 0 2 (-3)⟩ := by
  intro x y
  ext <;> simp only [Magma.op, op] <;> ring

theorem model_1313 (n : ℕ) [NeZero n] : Law1313.HasModel (n^4) := by
  exact hasModel_of_card (⟨op (-1) 0 2 (-3)⟩ : Magma (ZMod n × ZMod n × ZMod n × ZMod n))
    ((@Law1313.models_iff _ ⟨op (-1) 0 2 (-3)⟩).mpr law_1313) (by simp [pow_succ, Nat.mul_assoc])

spectrum_assert model_1313 complete

end Spectrum.QuarticSeeds

/-- info: 'Spectrum.QuarticSeeds.model_670' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.QuarticSeeds.model_670
/-- info: 'Spectrum.QuarticSeeds.model_1313' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spectrum.QuarticSeeds.model_1313
