import equational_theories.Spectrum.DupontTwists
import equational_theories.Spectrum.Linear

/-! All positive square orders for E1083 and E1110, and the cubic families
inherited by the Dupont twists. See `docs/open_spectra_survey_20260927.md`.
The square constructions use the Eisenstein and Fibonacci companion operators. -/

namespace Spectrum.QuadraticSeeds
open Law Law.MagmaLaw

def eisenstein {R : Type*} [CommRing R] (x y : R × R) : R × R :=
  (-x.2 - y.1, x.1 - x.2 - y.2)

def fibonacci {R : Type*} [CommRing R] (x y : R × R) : R × R :=
  (x.2 - y.1, x.1 + x.2 - y.2)

theorem law1083 {R : Type*} [CommRing R] :
    @Equation1083 (R × R) ⟨eisenstein⟩ := by
  intro x y
  apply Prod.ext <;> simp only [Magma.op, eisenstein] <;> ring

theorem law1110 {R : Type*} [CommRing R] :
    @Equation1110 (R × R) ⟨fibonacci⟩ := by
  intro x y
  apply Prod.ext <;> simp only [Magma.op, fibonacci] <;> ring

theorem square1083 (n : ℕ) [NeZero n] : Law1083.HasModel (n^2) := by
  exact hasModel_of_card (⟨eisenstein⟩ : Magma (ZMod n × ZMod n))
    ((@Law1083.models_iff _ ⟨eisenstein⟩).mpr law1083) (by simp [pow_two])

theorem square1110 (n : ℕ) [NeZero n] : Law1110.HasModel (n^2) := by
  exact hasModel_of_card (⟨fibonacci⟩ : Magma (ZMod n × ZMod n))
    ((@Law1110.models_iff _ ⟨fibonacci⟩).mpr law1110) (by simp [pow_two])

theorem dupont_cubes (n : ℕ) [NeZero n] :
    Law467.HasModel (n^3) ∧ Law704.HasModel (n^3) ∧ Law1110.HasModel (n^3) ∧
    Law1279.HasModel (n^3) ∧ Law1516.HasModel (n^3) :=
  DupontTwists.models (E63.cubic_idempotent n)

spectrum_assert square1083 complete
spectrum_assert square1110 complete
spectrum_assert dupont_cubes complete

/-- info: 'Spectrum.QuadraticSeeds.square1083' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square1083
end Spectrum.QuadraticSeeds
