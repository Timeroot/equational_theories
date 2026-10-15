import equational_theories.Spectrum.SmallOrders
import equational_theories.Spectrum.Equation66
import equational_theories.Spectrum.Equation167
import equational_theories.Spectrum.Definability

/-! Order eight refutes the previously unresolved spectrum inclusion
`Spec(E167) ⊆ Spec(E670)`. The corresponding finite FO-definability negative
was already known independently. -/
namespace Spectrum.SmallOrders

theorem model_167_8 : Law167.HasModel 8 := models_167 (by norm_num [residues])

theorem not_subspectral_167_670 : ¬ Law167.Subspectral Law670 :=
  fun h => not_order_670_8 (h.hasModel model_167_8)

theorem not_definableFin_167_670 : ¬ Law670.DefinableFromFin Law167 :=
  fun h => not_subspectral_167_670 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert model_167_8 complete
spectrum_assert not_subspectral_167_670 complete
spectrum_assert not_definableFin_167_670 complete

/-- Order ten supplies another directed spectrum separation. -/
theorem model_66_10 : Law66.HasModel 10 := models_66 (by norm_num [residues])

theorem not_subspectral_66_1083 : ¬ Law66.Subspectral Law1083 :=
  fun h => not_order_1083_10 (h.hasModel model_66_10)

theorem not_definableFin_66_1083 : ¬ Law1083.DefinableFromFin Law66 :=
  fun h => not_subspectral_66_1083 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert model_66_10 complete
spectrum_assert not_subspectral_66_1083 complete
spectrum_assert not_definableFin_66_1083 complete
end Spectrum.SmallOrders
