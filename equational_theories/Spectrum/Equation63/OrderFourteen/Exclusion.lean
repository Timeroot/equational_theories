import equational_theories.Spectrum.Equation63.OrderFourteen.CanonicalCertificate

/-! The order-fourteen exclusion: a general Latin-table reduction followed
by a compact, Lean-checked finite refutation. -/
namespace Spectrum

theorem not_order_63_14 : ¬ Law63.HasModel 14 := by
  rintro ⟨M,hM⟩
  obtain ⟨f,hf⟩ := @E63.OrderTen.cubic_of_e63 (Fin 14) _ M
    ((@Law63.models_iff _ M).mp hM)
  obtain ⟨g,hg,hd,hc,hfixed⟩ := E63.OrderFourteen.normalized_cubic f hf
  exact E63.OrderFourteen.RowTransfer.no_model
    E63.OrderFourteen.CanonicalCertificate.case_unsat
    E63.OrderFourteen.CanonicalCertificate.coverage_unsat g hg hd hc hfixed

spectrum_assert not_order_63_14 complete
end Spectrum
