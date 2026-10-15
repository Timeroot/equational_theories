import equational_theories.Spectrum.Equation63.OrderTen.Normalization
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A counting normalization. If every point has at most one left fixer,
then some non-idempotent row has at most one fixed point, unless all elements
are idempotent. This includes every finite quasigroup. -/
namespace Spectrum.SmallOrders.FewFixed

private def fixed {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A → A) (a : A) : Finset A := Finset.univ.filter fun x => f a x = x

theorem exists_few {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A → A)
    (hu : ∀ a b x, f a x = x → f b x = x → a = b)
    (hn : ∃ a, f a a ≠ a) :
    ∃ a, f a a ≠ a ∧ ∀ y z, f a y = y → f a z = z → y = z := by
  have hdis : (↑(Finset.univ : Finset A) : Set A).PairwiseDisjoint (fixed f) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hab (hu a b x (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)
  have hsum : ∑ a : A, (fixed f a).card ≤ Fintype.card A := by
    rw [← Finset.card_biUnion hdis]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  by_contra h
  have hlarge (a : A) (ha : f a a ≠ a) : 1 < (fixed f a).card := by
    by_contra hh
    have hc : (fixed f a).card ≤ 1 := by omega
    apply h
    refine ⟨a,ha,fun y z hy hz => ?_⟩
    exact Finset.card_le_one.mp hc y (by simp [fixed,hy]) z (by simp [fixed,hz])
  have hpos (a : A) : 1 ≤ (fixed f a).card := by
    by_cases ha : f a a = a
    · exact Finset.card_pos.mpr ⟨a,by simp [fixed,ha]⟩
    · exact Nat.le_of_lt (hlarge a ha)
  obtain ⟨a,ha⟩ := hn
  have hlt : ∑ _a : A, (1 : ℕ) < ∑ a : A, (fixed f a).card :=
    Finset.sum_lt_sum (fun a _ => hpos a) ⟨a, Finset.mem_univ a, hlarge a ha⟩
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hlt
  omega

def relabel {A : Type*} (f : A → A → A) (e : A ≃ A) : A → A → A :=
  fun x y => e (f (e.symm x) (e.symm y))

private theorem fixed_relabel {A : Type*} (f : A → A → A) (e : A ≃ A) (a : A)
    (h : ∀ y z, f (e.symm a) y = y → f (e.symm a) z = z → y = z) :
    ∀ y z, relabel f e a y = y → relabel f e a z = z → y = z := by
  intro y z hy hz
  apply e.symm.injective
  apply h
  · simpa [relabel] using congrArg e.symm hy
  · simpa [relabel] using congrArg e.symm hz

/-- The returned relabeling retains the usual first-row chain normalization. -/
theorem normalized {n : ℕ} [NeZero n] (f : Fin n → Fin n → Fin n)
    (hu : ∀ a b x, f a x = x → f b x = x → a = b) :
    ∃ e : Equiv.Perm (Fin n),
      let g := relabel f e
      (g 0 0 = 0 → ∀ x, g x x = x) ∧
      (∀ y, (g 0 y).val ≤ y.val + 1) ∧
      (g 0 0 ≠ 0 → ∀ y z, g 0 y = y → g 0 z = z → y = z) := by
  classical
  have choice : ∃ e : Equiv.Perm (Fin n),
      (relabel f e 0 0 = 0 → ∀ x, relabel f e x x = x) ∧
      (relabel f e 0 0 ≠ 0 → ∀ y z, relabel f e 0 y = y →
        relabel f e 0 z = z → y = z) := by
    by_cases hi : ∀ x, f x x = x
    · refine ⟨Equiv.refl _, ?_, ?_⟩
      · simpa [relabel] using (fun (_ : f 0 0 = 0) => hi)
      · simp [relabel,hi]
    · push Not at hi
      obtain ⟨a,ha,hfew⟩ := exists_few f hu hi
      let e := Equiv.swap a (0 : Fin n)
      have he : e.symm 0 = a := Equiv.swap_apply_right a 0
      refine ⟨e, fun hz => ?_, fun _ => fixed_relabel f e 0 ?_⟩
      · have heq : f a a = a := by
          apply e.injective
          simpa [relabel,he,e] using hz
        exact (ha heq).elim
      · simpa only [he] using hfew
  obtain ⟨e,hd,hfew⟩ := choice
  let g := relabel f e
  obtain ⟨q,hq,hchain⟩ := E63.OrderTen.exists_chain_label (g 0)
  have hqi : q.symm 0 = 0 := by apply q.injective; simpa using hq.symm
  have hcomp : relabel f (e.trans q) = relabel g q := by
    funext x y
    simp [g,relabel]
  have hz : relabel g q 0 0 = 0 ↔ g 0 0 = 0 := by
    change q (g (q.symm 0) (q.symm 0)) = 0 ↔ g 0 0 = 0
    rw [hqi]
    simpa only [hq] using (q.injective.eq_iff : q (g 0 0) = q 0 ↔ g 0 0 = 0)
  refine ⟨e.trans q, ?_⟩
  change (relabel f (e.trans q) 0 0 = 0 → _) ∧ _
  rw [hcomp]
  refine ⟨?_, ?_, ?_⟩
  · intro h0 x
    have hg : ∀ x, g x x = x := hd (hz.mp h0)
    simp only [relabel, hg, Equiv.apply_symm_apply]
  · intro y
    simpa only [relabel,hqi] using hchain y
  · intro h0
    apply fixed_relabel
    simpa only [hqi] using hfew (fun hg => h0 (hz.mpr hg))
end Spectrum.SmallOrders.FewFixed
