import equational_theories.Spectrum.Equation63.Induction
import equational_theories.Spectrum.Equation63.FiniteBasis
import equational_theories.Spectrum.Generated.Exclusion63_6

/-! # Constructive bounds for the spectrum of E63

The positive bound uses affine models, products, singular products, four finite
transversal designs, six table certificates, and an explicit cofinite induction.
There are no admitted steps in these positive results. See docs/63_lean_spectrum.md.
-/
namespace Spectrum.E63
open Law Law.MagmaLaw

/-- Every order at least 159 has an E63 model, without any external design theorem. -/
theorem all_large {n : ℕ} (hn : 159 ≤ n) : Law63.HasModel n := by
  apply cofinite_induction ?_ n hn
  intro m hm hs
  apply FiniteBasis.model hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  omega

theorem lower : positiveExcept {2,6,10,14,18,26,30,38,42,90,158} ⊆ Law63.spectrum := by
  rintro n ⟨hn, he⟩
  refine ⟨hn, ?_⟩
  by_cases hs : n < 1608
  · exact FiniteBasis.model hs he
  · exact all_large (by omega)

theorem cofinite : CofiniteSpectrum Law63 :=
  ⟨159, fun _ hn => ⟨by omega, all_large hn⟩⟩

/-- The two-element exclusion, checked over all sixteen tables by the kernel. -/
theorem not_two : ¬ Law63.HasModel 2 :=
  not_two_of_equation Law63 (@Equation63 (Fin 2))
    (@Law63.models_iff (Fin 2)) (by decide +kernel)

/-- The six-element exclusion reuses the existing checked finite refutation. -/
theorem proved_upper : Law63.spectrum ⊆ positiveExcept {2,6} := by
  rintro n ⟨hn, hM⟩
  refine ⟨hn, ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨fun he => not_two (he ▸ hM), fun he => not_order_63_6 (he ▸ hM)⟩

spectrum_assert not_two complete
spectrum_assert all_large complete
spectrum_assert lower complete
spectrum_assert cofinite complete
spectrum_assert proved_upper complete

end Spectrum.E63
