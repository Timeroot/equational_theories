import equational_theories.Spectrum.Equation467.OrderSixteen.Exclusion
import equational_theories.Spectrum.Equation1516Quartic
import equational_theories.Spectrum.Definability

/-! The order-sixteen witness for E1516 separates its spectrum from E467 and
obstructs even finite first-order definability of E467 from E1516. -/
namespace Spectrum

theorem not_subspectral_1516_467 : ¬ Law1516.Subspectral Law467 :=
  fun h => not_order_467_16 (h.hasModel E1516.model16)

theorem spectrum_467_ne_1516 : Law467.spectrum ≠ Law1516.spectrum :=
  fun h => not_subspectral_1516_467 h.symm.subset

theorem not_definableFin_1516_467 : ¬ Law467.DefinableFromFin Law1516 :=
  fun h => not_subspectral_1516_467 (Law.MagmaLaw.subspectral_of_definableFin h)

spectrum_assert not_subspectral_1516_467 complete
spectrum_assert spectrum_467_ne_1516 complete
spectrum_assert not_definableFin_1516_467 complete
end Spectrum
