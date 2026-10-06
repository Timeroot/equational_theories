import equational_theories.Spectrum.Equation63.OrderTen.Basic
import Mathlib.Tactic.Push

/-!
The symmetry breaking here is proved for every finite size, without enumerating
permutations. Traverse a function's arrows, assigning each new vertex the next
unused label. The resulting function satisfies `f i ≤ i+1` and keeps 0 fixed.

For a permutation this simply labels its cycles consecutively. The induction
below implements this with swaps: when processing i, swap f(i) with i+1 if
necessary. Earlier inputs and outputs are at most i, so they are unaffected.
-/
namespace Spectrum.E63.OrderTen

theorem exists_chain_label {n : ℕ} [NeZero n] (f : Fin n → Fin n) :
    ∃ e : Equiv.Perm (Fin n), e 0 = 0 ∧
      ∀ i, (e (f (e.symm i))).val ≤ i.val + 1 := by
  have aux (k : ℕ) : ∃ e : Equiv.Perm (Fin n), e 0 = 0 ∧
      ∀ i, i.val < k → (e (f (e.symm i))).val ≤ i.val + 1 := by
    induction k with
    | zero => exact ⟨Equiv.refl _, rfl, by simp⟩
    | succ k ih =>
      obtain ⟨e, he, hf⟩ := ih
      by_cases hk : k < n
      · let i : Fin n := ⟨k, hk⟩
        let g (j : Fin n) := e (f (e.symm j))
        by_cases hi : (g i).val ≤ k + 1
        · refine ⟨e, he, fun j hj => ?_⟩
          by_cases hjk : j.val < k
          · exact hf j hjk
          · have hji : j = i := Fin.ext (by dsimp [i]; omega)
            subst j
            exact hi
        · have ha : k + 1 < n := by have := (g i).isLt; omega
          let a : Fin n := ⟨k + 1, ha⟩
          let s := Equiv.swap a (g i)
          have fixed (j : Fin n) (hj : j.val ≤ k) : s j = j := by
            apply Equiv.swap_apply_of_ne_of_ne <;> intro hh
            · have := congrArg Fin.val hh
              dsimp [a] at this
              omega
            · have := congrArg Fin.val hh
              omega
          have h0 : s 0 = 0 := fixed 0 (by simp)
          refine ⟨e.trans s, by simpa only [Equiv.trans_apply, he] using h0, fun j hj => ?_⟩
          change (s (g (s j))).val ≤ j.val + 1
          rw [fixed j (by omega)]
          by_cases hjk : j.val < k
          · rw [fixed (g j) (by have := hf j hjk; change (g j).val ≤ j.val + 1 at this; omega)]
            exact hf j hjk
          · have hji : j = i := Fin.ext (by dsimp [i]; omega)
            subst j
            change (Equiv.swap a (g i) (g i)).val ≤ k + 1
            rw [Equiv.swap_apply_right]
      · exact ⟨e, he, fun j _ => hf j (by omega)⟩
  obtain ⟨e, he, hf⟩ := aux n
  exact ⟨e, he, fun i => hf i i.isLt⟩

/-- Choose a non-idempotent element as 0 if there is one, then label the
cycles of its left translation consecutively. The conditional diagonal rule
combines the globally idempotent and non-idempotent cases in one certificate. -/
theorem normalized_cubic (f : Fin 10 → Fin 10 → Fin 10) (h : Cubic f) :
    ∃ g : Fin 10 → Fin 10 → Fin 10, Cubic g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) ∧ (∀ y, (g 0 y).val ≤ y.val + 1) := by
  classical
  have choose_zero : ∃ g : Fin 10 → Fin 10 → Fin 10, Cubic g ∧
      (g 0 0 = 0 → ∀ x, g x x = x) := by
    by_cases hi : ∀ x, f x x = x
    · exact ⟨f, h, fun _ => hi⟩
    · push Not at hi
      obtain ⟨x, hx⟩ := hi
      let e := Equiv.swap x (0 : Fin 10)
      let g (a b : Fin 10) := e (f (e.symm a) (e.symm b))
      refine ⟨g, cubic_relabel h e, fun hg => ?_⟩
      have he : e.symm 0 = x := Equiv.swap_apply_right x 0
      have : f x x = x := by
        apply e.injective
        simpa only [g, he, e, Equiv.swap_apply_left] using hg
      exact (hx this).elim
  obtain ⟨g, hg, hi⟩ := choose_zero
  obtain ⟨e, he, hc⟩ := exists_chain_label (g 0)
  have he' : e.symm 0 = 0 := by
    apply e.injective
    simpa using he.symm
  let q (a b : Fin 10) := e (g (e.symm a) (e.symm b))
  refine ⟨q, cubic_relabel hg e, ?_, ?_⟩
  · intro hq x
    have h0 : g 0 0 = 0 := by
      apply e.injective
      simpa only [q, he', he] using hq
    simp only [q, hi h0, Equiv.apply_symm_apply]
  · intro y
    simpa only [q, he'] using hc y

end Spectrum.E63.OrderTen
