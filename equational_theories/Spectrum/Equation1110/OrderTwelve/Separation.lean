import equational_theories.Spectrum.Equation1110.OrderTwelve.Exclusion
import equational_theories.Spectrum.Equation167
import equational_theories.Spectrum.Definability

/-! Order twelve refutes the previously open inclusion of the E167 spectrum
in the E1110 spectrum, and therefore the corresponding finite definability. -/
namespace Spectrum.E1110.OrderTwelve

theorem model_167_12 : Law167.HasModel 12 := models_167 (by norm_num [residues])

theorem not_subspectral_167_1110 : ¬ Law167.Subspectral Law1110 :=
  fun h => not_order_1110_12 (h.hasModel model_167_12)

theorem not_definableFin_167_1110 : ¬ Law1110.DefinableFromFin Law167 :=
  fun h => not_subspectral_167_1110 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert model_167_12 complete
spectrum_assert not_subspectral_167_1110 complete
spectrum_assert not_definableFin_167_1110 complete

end Spectrum.E1110.OrderTwelve
