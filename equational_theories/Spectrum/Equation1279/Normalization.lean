import equational_theories.Spectrum.Equation1110.RowNormalization

/-! Squaring has no two-cycle in a finite E1279 magma. After conjugating
squaring to a canonical permutation, labels outside its support remain free;
these normalize the first row without changing squaring. -/
namespace Spectrum.E1279
open SmallOrders

lemma square_two_cycle {A : Type*} [Finite A] {f : A → A → A}
    (h : Holds .e1279 f) {a b : A} (ha : f a a = b) (hb : f b b = a) : a = b := by
  have hba : f b a = a := (left_bijective h a).1 (by
    simpa only [Holds, middle, first, inner, last, ha, hb] using h b a)
  have hab : f a b = b := (left_bijective h b).1 (by
    simpa only [Holds, middle, first, inner, last, ha, hb] using h a b)
  have hh := h a a
  simpa only [Holds, middle, first, inner, last, ha, hba, hab] using hh.symm

theorem normalize_supported_row {n : ℕ} [NeZero n] (k : ℕ)
    (hk : 2 ≤ k) (hn : k ≤ n)
    (d : Equiv.Perm (Fin n)) (hzero : d 0 = 1)
    (hfix : ∀ x : Fin n, k ≤ x.val → d x = x)
    (f : Fin n → Fin n → Fin n) (h : Holds .e1279 f)
    (hD : ∀ x, f x x = d x) :
    ∃ g : Fin n → Fin n → Fin n,
      Holds .e1279 g ∧ (∀ x, g x x = d x) ∧
      (∀ y, (g 0 y).val ≤ y.val + (k - 1)) := by
  have h00 : f 0 0 = 1 := (hD 0).trans hzero
  have hprefix : ∀ i : Fin n, i.val < 1 → (f 0 i).val ≤ i.val + (k - 1) := by
    intro i hi
    have hi0 : i = 0 := Fin.ext (by simp_all)
    subst i
    rw [h00]
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
    omega
  obtain ⟨e, he, hc⟩ := E1110.RowNormalization.chain_label_prefix_offset
    (f 0) 1 (k - 1) (by omega) hprefix
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
end Spectrum.E1279
