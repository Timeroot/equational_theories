import equational_theories.Spectrum.Equation467.OrderSixteen.RotatedEncoding
import equational_theories.Spectrum.Equation467.OrderSixteen.Certificates

/-! The complete order-sixteen exclusion: mathematical normalization and
encoding soundness, followed by saved, Lean-checked LRAT refutations. -/
namespace Spectrum

theorem not_order_467_16 : ¬ Law467.HasModel 16 :=
  E467.OrderSixteen.exclusion_of_optimized E467.OrderSixteen.useRotation
    E467.OrderSixteen.all_unsat

spectrum_assert not_order_467_16 complete
end Spectrum
