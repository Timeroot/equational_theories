import equational_theories.Spectrum.Equation467.OrderSixteen.Separation

/-- E1516 has an order-sixteen model; E467 has none. -/
theorem Equation467_not_definableFromFin_Equation1516 : ¬ Law467.DefinableFromFin Law1516 :=
  Spectrum.not_definableFin_1516_467

spectrum_assert Equation467_not_definableFromFin_Equation1516 complete
