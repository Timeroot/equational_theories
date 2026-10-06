import equational_theories.Spectrum.Equation667Twelve.Separation

/-- E481 has an order-twelve model; E667 has none. -/
theorem Equation667_not_definableFromFin_Equation481 : ¬ Law667.DefinableFromFin Law481 :=
  Spectrum.not_definableFin_481_667

spectrum_assert Equation667_not_definableFromFin_Equation481 complete
