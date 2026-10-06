import equational_theories.Spectrum.Equation63.OrderTen.Exclusion
import equational_theories.Spectrum.Equation115Construction
import equational_theories.Spectrum.Definability

/-! Order ten separates the spectra of E115 and E63, and therefore rules out
even finite first-order definability of E63 from E115. -/
namespace Spectrum

theorem not_subspectral_115_63 : ¬ Law115.Subspectral Law63 := by
  intro h
  exact not_order_63_10 (h.hasModel (models_115 (n := 10) (by simp [positiveExcept])))

theorem spectrum_63_ne_115 : Law63.spectrum ≠ Law115.spectrum := by
  intro h
  exact not_subspectral_115_63 h.symm.subset

theorem not_definableFin_115_63 : ¬ Law63.DefinableFromFin Law115 :=
  fun h => not_subspectral_115_63 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_115_63 complete
spectrum_assert spectrum_63_ne_115 complete
spectrum_assert not_definableFin_115_63 complete
end Spectrum
