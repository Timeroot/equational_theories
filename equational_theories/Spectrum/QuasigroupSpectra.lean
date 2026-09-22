import equational_theories.Spectrum.Equation115Construction
import equational_theories.Spectrum.Equation481Construction
import equational_theories.Spectrum.QuasigroupSix
import equational_theories.Spectrum.Generated.ImplicationTransfer

/-! Exact spectra of E115, E481, and E873: cyclic constructions and finite exclusions. -/
namespace Spectrum

theorem not_order_115_6 : ¬ Law115.HasModel 6 := by
  rintro ⟨M,hM⟩
  exact QuasigroupSix.impossible115 M ((@Law115.models_iff _ M).mp hM)
spectrum_assert not_order_115_6 complete

theorem not_order_481_6 : ¬ Law481.HasModel 6 := by
  rintro ⟨M,hM⟩
  exact QuasigroupSix.impossible481 M ((@Law481.models_iff _ M).mp hM)
spectrum_assert not_order_481_6 complete

theorem not_order_873_6 : ¬ Law873.HasModel 6 := by
  rintro ⟨M,hM⟩
  exact QuasigroupSix.impossible873 M ((@Law873.models_iff _ M).mp hM)
spectrum_assert not_order_873_6 complete

theorem spectrum_115 : Law115.spectrum = positiveExcept {2,6} := by
  apply Set.Subset.antisymm
  · rintro n ⟨hn,hM⟩
    refine ⟨hn, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => not_two_115 (h ▸ hM), fun h => not_order_115_6 (h ▸ hM)⟩
  · intro n hn
    exact ⟨hn.1, models_115 hn⟩
spectrum_assert spectrum_115 complete

theorem spectrum_481 : Law481.spectrum = positiveExcept {3,6} := by
  apply Set.Subset.antisymm
  · rintro n ⟨hn,hM⟩
    refine ⟨hn, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => not_three_481 (h ▸ hM), fun h => not_order_481_6 (h ▸ hM)⟩
  · intro n hn
    exact ⟨hn.1, models_481 hn⟩
spectrum_assert spectrum_481 complete

theorem spectrum_873 : Law873.spectrum = positiveExcept {2,6} := by
  apply Set.Subset.antisymm
  · rintro n ⟨hn,hM⟩
    refine ⟨hn, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => not_two_873 (h ▸ hM), fun h => not_order_873_6 (h ▸ hM)⟩
  · rw [← spectrum_115]
    exact ImplicationTransfer.path_115_873
spectrum_assert spectrum_873 complete

end Spectrum
