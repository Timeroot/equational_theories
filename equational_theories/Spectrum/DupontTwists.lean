import equational_theories.Spectrum.Equation63.FieldTail

/-! Idempotent Dupont models transfer to five further spectrum families.
The explicit E63 tail gives cutoff 1228 for each, without Wilson's theorem.
See `docs/open_spectra_survey_20260927.md`. -/

namespace Spectrum.DupontTwists

theorem models {n : ℕ} (h : E63.Model (Fin n) true) :
    Law467.HasModel n ∧ Law704.HasModel n ∧ Law1110.HasModel n ∧
    Law1279.HasModel n ∧ Law1516.HasModel n := by
  obtain ⟨p, hp, hi⟩ := h
  have ip (x) : p x x = x := hi rfl x
  let q := fun x y => p y (p y x)
  have pq (x y) : p x (q x y) = y := hp y x
  have qp (x y) : q x (p x y) = y := by
    apply E63.injective_left hp x
    rw [pq]
  have iq (x) : q x x = x := by simp [q, ip]
  have q73 (x y) : q y (q y (q x y)) = x := by
    change q y (q y (p y (p y x))) = x
    rw [qp, qp]
  have q125 (x y) : q y (q (q y x) y) = x := by
    change q y (p y (p y (q y x))) = x
    rw [pq, qp]
  have r118 (x y) : q (q y (q y x)) y = x := by
    change p y (p y (q y (q y x))) = x
    rw [pq, pq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨p⟩, (@Law467.models_iff _ ⟨p⟩).mpr ?_⟩
    intro x y
    change x = p y (p x (p x (p y y)))
    rw [ip]
    exact (hp x y).symm
  · refine ⟨⟨q⟩, (@Law704.models_iff _ ⟨q⟩).mpr ?_⟩
    intro x y
    change x = q y (q y (q (q x x) y))
    rw [iq, q73]
  · refine ⟨⟨q⟩, (@Law1110.models_iff _ ⟨q⟩).mpr ?_⟩
    intro x y
    change x = q y (q (q y (q x x)) y)
    rw [iq, q125]
  · refine ⟨⟨fun x y => q y x⟩, (@Law1279.models_iff _ ⟨fun x y => q y x⟩).mpr ?_⟩
    intro x y
    change x = q (q y (q y (q x x))) y
    rw [iq, r118]
  · refine ⟨⟨p⟩, (@Law1516.models_iff _ ⟨p⟩).mpr ?_⟩
    intro x y
    change x = p (p y y) (p x (p x y))
    rw [ip]
    exact (hp x y).symm

theorem all_large {n : ℕ} (hn : 1228 ≤ n) :
    Law467.HasModel n ∧ Law704.HasModel n ∧ Law1110.HasModel n ∧
    Law1279.HasModel n ∧ Law1516.HasModel n := models (E63.FieldBounds.all_large hn)

theorem cofinite_467 : CofiniteSpectrum Law467 :=
  ⟨1228, fun _ hn => ⟨by omega, (all_large hn).1⟩⟩
theorem cofinite_704 : CofiniteSpectrum Law704 :=
  ⟨1228, fun _ hn => ⟨by omega, (all_large hn).2.1⟩⟩
theorem cofinite_1110 : CofiniteSpectrum Law1110 :=
  ⟨1228, fun _ hn => ⟨by omega, (all_large hn).2.2.1⟩⟩
theorem cofinite_1279 : CofiniteSpectrum Law1279 :=
  ⟨1228, fun _ hn => ⟨by omega, (all_large hn).2.2.2.1⟩⟩
theorem cofinite_1516 : CofiniteSpectrum Law1516 :=
  ⟨1228, fun _ hn => ⟨by omega, (all_large hn).2.2.2.2⟩⟩

/-- info: 'Spectrum.DupontTwists.cofinite_467' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cofinite_467
/-- info: 'Spectrum.DupontTwists.cofinite_1279' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cofinite_1279
end Spectrum.DupontTwists
