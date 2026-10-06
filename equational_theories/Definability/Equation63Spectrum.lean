import equational_theories.Spectrum.Equation63.OrderTen.Separation

/-! Register the order-ten spectrum obstruction with the definability board.
E115 has a ten-element model, whereas E63 has none. -/

theorem Equation63_not_definableFromFin_Equation115 : ¬ Law63.DefinableFromFin Law115 :=
  Spectrum.not_definableFin_115_63

spectrum_assert Equation63_not_definableFromFin_Equation115 complete
