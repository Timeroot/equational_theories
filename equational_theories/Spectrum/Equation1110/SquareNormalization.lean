import equational_theories.Spectrum.Equation1110.Diagonal

/-! Label the squaring permutation consecutively, choosing a non-idempotent
zero whenever one exists. Unlike the ordinary chain-law normalization, this
normalizes the diagonal rather than a left translation. -/
namespace Spectrum.E1110.SquareNormalization
open SmallOrders

theorem normalized {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f) :
    ∃ g : Fin n → Fin n → Fin n, Holds .e1110 g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧ (∀ y, (g y y).val ≤ y.val + 1) := by
  classical
  have choose_zero : ∃ g : Fin n → Fin n → Fin n, Holds .e1110 g ∧
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
  obtain ⟨e, he, hc⟩ := E63.OrderTen.exists_chain_label (fun x => g x x)
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

end Spectrum.E1110.SquareNormalization
