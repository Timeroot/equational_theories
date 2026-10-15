import equational_theories.Spectrum.Equation1110.ForwardEncoding

/-! Normalize a left translation while preserving a short nontrivial part of
its squaring permutation. The already proved E8 identity makes the first two
entries of row zero a transposition. Traversing the remaining labels while
fixing the support of squaring gives a uniform bound on every later row entry. -/
namespace Spectrum.E1110.RowNormalization
open SmallOrders

/-- Extend an already normalized prefix with a fixed allowance `s₀`, keeping
all labels below `k₀ + s₀` fixed. At step `k`, only labels at least `k + s₀`
are swapped, so every earlier normalized input and output is unchanged. -/
theorem chain_label_prefix_offset {n : ℕ} (f : Fin n → Fin n) (k₀ s₀ : ℕ)
    (hs : 0 < s₀)
    (hprefix : ∀ i, i.val < k₀ → (f i).val ≤ i.val + s₀) :
    ∃ e : Equiv.Perm (Fin n), (∀ i, i.val < k₀ + s₀ → e i = i) ∧
      ∀ i, (e (f (e.symm i))).val ≤ i.val + s₀ := by
  classical
  have aux (t : ℕ) : ∃ e : Equiv.Perm (Fin n), (∀ i, i.val < k₀ + s₀ → e i = i) ∧
      ∀ i, i.val < k₀ + t → (e (f (e.symm i))).val ≤ i.val + s₀ := by
    induction t with
    | zero => exact ⟨Equiv.refl _, fun _ _ => rfl, by simpa using hprefix⟩
    | succ t ih =>
      obtain ⟨e, he, hf⟩ := ih
      let k := k₀ + t
      by_cases hk : k < n
      · let i : Fin n := ⟨k, hk⟩
        let g (j : Fin n) := e (f (e.symm j))
        by_cases hi : (g i).val ≤ k + s₀
        · refine ⟨e, he, fun j hj => ?_⟩
          by_cases hjk : j.val < k
          · exact hf j hjk
          · have hji : j = i := Fin.ext (by dsimp [i, k] at *; omega)
            subst j
            exact hi
        · have ha : k + s₀ < n := by have := (g i).isLt; omega
          let a : Fin n := ⟨k + s₀, ha⟩
          let s := Equiv.swap a (g i)
          have fixed (j : Fin n) (hj : j.val < k + s₀) : s j = j := by
            apply Equiv.swap_apply_of_ne_of_ne <;> intro hh
            · have := congrArg Fin.val hh
              dsimp [a] at this
              omega
            · have := congrArg Fin.val hh
              omega
          refine ⟨e.trans s, ?_, fun j hj => ?_⟩
          · intro j hj
            change s (e j) = j
            rw [he j hj, fixed j (by dsimp [k]; omega)]
          · change (s (g (s j))).val ≤ j.val + s₀
            rw [fixed j (by dsimp [k] at *; omega)]
            by_cases hjk : j.val < k
            · rw [fixed (g j) (by have := hf j hjk; change (g j).val ≤ j.val + s₀ at this; omega)]
              exact hf j hjk
            · have hji : j = i := Fin.ext (by dsimp [i, k] at *; omega)
              subst j
              change (Equiv.swap a (g i) (g i)).val ≤ k + s₀
              rw [Equiv.swap_apply_right]
      · exact ⟨e, he, fun j _ => hf j (by dsimp [k] at *; omega)⟩
  obtain ⟨e, he, hf⟩ := aux n
  exact ⟨e, he, fun i => hf i (by have := i.isLt; omega)⟩

theorem chain_label_prefix {n : ℕ} (f : Fin n → Fin n) (k₀ : ℕ)
    (hprefix : ∀ i, i.val < k₀ → (f i).val ≤ i.val + 1) :
    ∃ e : Equiv.Perm (Fin n), (∀ i, i.val ≤ k₀ → e i = i) ∧
      ∀ i, (e (f (e.symm i))).val ≤ i.val + 1 := by
  obtain ⟨e, he, hc⟩ := chain_label_prefix_offset f k₀ 1 (by omega) hprefix
  exact ⟨e, fun i hi => he i (by omega), hc⟩

/-- Simultaneously normalize row zero and a squaring map supported on labels
below `k`. The row allowance `k - 2` preserves this entire support, while E8
already bounds the first two entries. This holds for every finite order. -/
theorem normalize_supported_row {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 3 ≤ k) (hn : k ≤ n)
    (d : Equiv.Perm (Fin n)) (hzero : d 0 = 1)
    (hfix : ∀ x : Fin n, k ≤ x.val → d x = x)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hD : ∀ x, f x x = d x) :
    ∃ g : Fin n → Fin n → Fin n,
      Holds .e1110 g ∧ (∀ x, g x x = d x) ∧
      (∀ y, (g 0 y).val ≤ y.val + (k - 2)) := by
  have h00 : f 0 0 = 1 := (hD 0).trans hzero
  have h01 : f 0 1 = 0 := by simpa [h00] using ForwardEncoding.forward_identity f h 0
  have hprefix : ∀ i : Fin n, i.val < 2 → (f 0 i).val ≤ i.val + (k - 2) := by
    intro i hi
    have hh : i = 0 ∨ i = 1 := by
      have hone : (1 : Fin n).val = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      have hz : (0 : Fin n).val = 0 := rfl
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with hi | hi
      · exact Or.inl (Fin.ext (hi.trans hz.symm))
      · exact Or.inr (Fin.ext (hi.trans hone.symm))
    rcases hh with rfl | rfl
    · have hv : (f 0 0).val = 1 := by rw [h00]; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
      have hz : (0 : Fin n).val = 0 := rfl
      omega
    · rw [h01]; simp
  obtain ⟨e, he, hc⟩ := chain_label_prefix_offset (f 0) 2 (k - 2) (by omega) hprefix
  have he0 : e 0 = 0 := he 0 (by simp)
  have he0' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
  have commutes (x : Fin n) : e (d x) = d (e x) := by
    by_cases hx : x.val < k
    · have hdx : (d x).val < k := by
        by_contra hh
        have hh' : d (d x) = d x := hfix (d x) (by omega)
        have hh'' : d x = x := d.injective hh'
        rw [hh''] at hh
        exact hh hx
      rw [he x (by omega), he (d x) (by omega)]
    · have hex : k ≤ (e x).val := by
        by_contra hh
        have heex := he (e x) (by omega)
        have hexx : e x = x := e.injective heex
        rw [hexx] at hh
        omega
      rw [hfix x (by omega), hfix (e x) hex]
  let g (x y : Fin n) := e (f (e.symm x) (e.symm y))
  refine ⟨g, holds_relabel h e, ?_, ?_⟩
  · intro x
    change e (f (e.symm x) (e.symm x)) = d x
    rw [hD, commutes, e.apply_symm_apply]
  · intro y
    simpa only [g, he0'] using hc y

/-- A three-cycle permits the ordinary row-chain bound. -/
theorem normalize_three_row {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (d : Equiv.Perm (Fin n)) (hzero : d 0 = 1)
    (hfix : ∀ x : Fin n, 3 ≤ x.val → d x = x)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hD : ∀ x, f x x = d x) :
    ∃ g : Fin n → Fin n → Fin n,
      Holds .e1110 g ∧ (∀ x, g x x = d x) ∧
      (∀ y, (g 0 y).val ≤ y.val + 1) :=
  normalize_supported_row 3 le_rfl hn d hzero hfix f h hD

/-- A four-cycle permits one extra position in the row-chain bound. -/
theorem normalize_four_row {n : ℕ} [NeZero n] (hn : 4 ≤ n)
    (d : Equiv.Perm (Fin n)) (hzero : d 0 = 1)
    (hfix : ∀ x : Fin n, 4 ≤ x.val → d x = x)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1110 f)
    (hD : ∀ x, f x x = d x) :
    ∃ g : Fin n → Fin n → Fin n,
      Holds .e1110 g ∧ (∀ x, g x x = d x) ∧
      (∀ y, (g 0 y).val ≤ y.val + 2) :=
  normalize_supported_row 4 (by omega) hn d hzero hfix f h hD

end Spectrum.E1110.RowNormalization
