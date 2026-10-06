import equational_theories.Spectrum.Equation667Twelve.Exclusion
import equational_theories.Spectrum.Equation481Construction
import equational_theories.Spectrum.Definability

/-! Order twelve separates E481 from E667, even at the level of spectra. -/
namespace Spectrum

theorem not_subspectral_481_667 : ¬ Law481.Subspectral Law667 := by
  intro h
  exact not_order_667_12 (h.hasModel (models_481 (n := 12) (by simp [positiveExcept])))

theorem spectrum_667_ne_481 : Law667.spectrum ≠ Law481.spectrum :=
  fun h => not_subspectral_481_667 h.symm.subset

theorem not_definableFin_481_667 : ¬ Law667.DefinableFromFin Law481 :=
  fun h => not_subspectral_481_667 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_481_667 complete
spectrum_assert spectrum_667_ne_481 complete
spectrum_assert not_definableFin_481_667 complete
end Spectrum
