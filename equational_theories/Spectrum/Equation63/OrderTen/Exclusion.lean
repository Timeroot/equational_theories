import equational_theories.Spectrum.Equation63.OrderTen.Certificate

/-! The order-ten exclusion, assembled from the mathematical reductions and
one cached, Lean-checked LRAT certificate. No pending theorem is imported. -/
namespace Spectrum

theorem not_order_63_10 : ¬ Law63.HasModel 10 := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf⟩ := @E63.OrderTen.cubic_of_e63 (Fin 10) _ M
    ((@Law63.models_iff _ M).mp hM)
  obtain ⟨g, hg, hd, hc⟩ := E63.OrderTen.normalized_cubic f hf
  exact E63.OrderTen.Encoding.no_model_of_unsat E63.OrderTen.unsat g hg hd hc

spectrum_assert not_order_63_10 complete
end Spectrum
