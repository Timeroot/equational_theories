import equational_theories.Spectrum.Equation907.PointedCycles
import equational_theories.Spectrum.Equation63.OrderTen.Normalization

/-! Relabeling reduction for E907; the idempotent case is retained. -/
namespace Spectrum.E907.OrderTen
abbrev Holds {A : Type*} (f : A → A → A) := @Equation907 A ⟨f⟩

theorem holds_relabel {A : Type*} {f : A → A → A}
    (h : Holds f) (e : A ≃ A) : Holds (fun x y => e (f (e.symm x) (e.symm y))) := by
  intro x y
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    using congrArg e (h (e.symm x) (e.symm y))

/-- Normalize a model by selecting a non-idempotent 0 if one exists, then
labelling the cycles of its left translation consecutively. Both steps are
proved for arbitrary sizes; no permutations are enumerated. -/
theorem normalized {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin n) (h : Holds f) :
    ∃ g : Fin n → Fin n → Fin n, Holds g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧ (∀ y, (g 0 y).val ≤ y.val + 1) := by
  classical
  have choose_zero : ∃ g : Fin n → Fin n → Fin n, Holds g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) := by
    by_cases hi : ∀ x, f x x = x
    · exact ⟨f, h, fun _ => hi⟩
    · push Not at hi
      obtain ⟨x, hx⟩ := hi
      let e := Equiv.swap x (0 : Fin n)
      let g (a b : Fin n) := e (f (e.symm a) (e.symm b))
      refine ⟨g, holds_relabel h e, fun hg => ?_⟩
      have he : e.symm 0 = x := Equiv.swap_apply_right x 0
      have : f x x = x := by
        apply e.injective
        simpa only [g, he, e, Equiv.swap_apply_left] using hg
      exact (hx this).elim
  obtain ⟨g, hg, hi⟩ := choose_zero
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he.symm
  let q (a b : Fin n) := e (g (e.symm a) (e.symm b))
  refine ⟨q, holds_relabel hg e, ?_, ?_⟩
  · intro hq x
    have h0 : g 0 0 = 0 := by
      apply e.injective
      simpa only [q, he', he] using hq
    simp only [q, hi h0, Equiv.apply_symm_apply]
  · intro y
    simpa only [q, he'] using hc y

end Spectrum.E907.OrderTen
