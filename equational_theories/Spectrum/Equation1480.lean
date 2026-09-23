import equational_theories.Spectrum.Equation1480Construction
import equational_theories.Spectrum.Generated.SmallOrder
import equational_theories.Spectrum.Shapes

/-! The exact E1480 spectrum: all positive orders other than 2 and 3. -/
namespace Spectrum

theorem models_1480 {n : ℕ} (h2 : n ≠ 2) (h3 : n ≠ 3) : Law1480.HasModel n := by
  by_cases h0 : n = 0
  · subst n; exact Law1480.hasModel_zero
  by_cases h1 : n = 1
  · subst n; exact Law1480.hasModel_one
  by_cases he : n % 2 = 0
  · have hc : 4 + 2 * ((n-4)/2) = n := by omega
    exact hc ▸ Construction1480.even_models ((n-4)/2)
  · have hc : 5 + 2 * ((n-5)/2) = n := by omega
    exact hc ▸ Construction1480.odd_models ((n-5)/2)

theorem spectrum_1480 : Law1480.spectrum = positiveExcept {2,3} := by
  apply Set.Subset.antisymm
  · rintro n ⟨hn,hM⟩
    refine ⟨hn, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => not_two_1480 (h ▸ hM), fun h => not_order_1480_3 (h ▸ hM)⟩
  · intro n hn
    have h : 0 < n ∧ n ≠ 2 ∧ n ≠ 3 := by simpa [positiveExcept] using hn
    exact ⟨h.1,models_1480 h.2.1 h.2.2⟩

spectrum_assert models_1480 complete
spectrum_assert spectrum_1480 complete
end Spectrum
