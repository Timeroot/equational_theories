import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push

/-! Symmetry breaking by first occurrence in a finite multiplication table.

Choose the lexicographically least relabelling fixing an initial segment.
If the labels `a < b` have not yet been used as inputs, and `a` has not yet
appeared as an output, the next new output cannot be `b`: swapping the two
labels would make the table smaller. No algebraic identity is assumed.
-/
namespace Spectrum.FiniteSearch

/-- Transport a multiplication table along a permutation. -/
def relabel {n : ℕ} (f : Fin n → Fin n → Fin n) (e : Equiv.Perm (Fin n))
    (x y : Fin n) : Fin n := e (f (e.symm x) (e.symm y))

/-- First-use normalization for an arbitrary ordered list of table cells.
The implication only applies when every input inspected so far is below
`a`; this includes the growing-square traversal used by the E467 search.
The permutation fixes all labels below `k`.
-/
theorem exists_first_use {n m : ℕ} (f : Fin n → Fin n → Fin n)
    (cells : Fin m → Fin n × Fin n) (k : ℕ) :
    ∃ e : Equiv.Perm (Fin n), (∀ x : Fin n, x.val < k → e x = x) ∧
      ∀ (i : Fin m) (a b : Fin n), k ≤ a.val → a < b →
        (∀ j ≤ i, (cells j).1 < a ∧ (cells j).2 < a) →
        relabel f e (cells i).1 (cells i).2 = b →
        ∃ j < i, relabel f e (cells j).1 (cells j).2 = a := by
  classical
  let S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter
    (fun e => ∀ x : Fin n, x.val < k → e x = x)
  let key (e : Equiv.Perm (Fin n)) : Lex (Fin m → Fin n) :=
    toLex (fun i => relabel f e (cells i).1 (cells i).2)
  obtain ⟨e, he, hmin⟩ := S.exists_min_image key ⟨Equiv.refl _, by simp [S]⟩
  have hfix : ∀ x : Fin n, x.val < k → e x = x := (Finset.mem_filter.mp he).2
  refine ⟨e, hfix, ?_⟩
  intro i a b hka hab hin hi
  by_contra! hnone
  let g := relabel f e
  let candidates : Finset (Fin m) := Finset.univ.filter
    (fun j => j ≤ i ∧ g (cells j).1 (cells j).2 = b)
  have hnon : candidates.Nonempty := ⟨i, by simp [candidates, g, hi]⟩
  let j := candidates.min' hnon
  have hjmem := candidates.min'_mem hnon
  have hji : j ≤ i := (Finset.mem_filter.mp hjmem).2.1
  have hjb : g (cells j).1 (cells j).2 = b := (Finset.mem_filter.mp hjmem).2.2
  let s := Equiv.swap a b
  have sfixed (x : Fin n) (hx : x < a) : s x = x := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact ne_of_lt hx
    · exact ne_of_lt (hx.trans hab)
  have hnew : e.trans s ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x hx
    rw [Equiv.trans_apply, hfix x hx]
    exact sfixed x (show x.val < a.val by omega)
  have smaller : key (e.trans s) < key e := by
    refine ⟨j, ?_, ?_⟩
    · intro t ht
      have hti : t ≤ i := (le_of_lt ht).trans hji
      have hf1 := sfixed (cells t).1 (hin t hti).1
      have hf2 := sfixed (cells t).2 (hin t hti).2
      change s (g (s (cells t).1) (s (cells t).2)) = g (cells t).1 (cells t).2
      rw [hf1, hf2]
      apply Equiv.swap_apply_of_ne_of_ne
      · exact hnone t (lt_of_lt_of_le ht hji)
      · intro heq
        have htm : t ∈ candidates := by simp [candidates, hti, heq]
        have := candidates.min'_le t htm
        exact (not_le_of_gt ht) this
    · change s (g (s (cells j).1) (s (cells j).2)) < g (cells j).1 (cells j).2
      rw [sfixed (cells j).1 (hin j hji).1, sfixed (cells j).2 (hin j hji).2,
        hjb, Equiv.swap_apply_right]
      exact hab
  exact (not_lt_of_ge (hmin _ hnew)) smaller

/-- A permutation fixing the support of a map commutes with that map. The
initial segment formulation is convenient for a prescribed squaring cycle. -/
theorem commute_of_fixed_initial {n : ℕ} (d : Fin n → Fin n) (k : ℕ)
    (hd : ∀ x, k ≤ x.val → d x = x)
    (hk : ∀ x, x.val < k → (d x).val < k)
    (e : Equiv.Perm (Fin n)) (he : ∀ x, x.val < k → e x = x) :
    ∀ x, e (d x) = d (e x) := by
  intro x
  by_cases hx : x.val < k
  · rw [he x hx, he (d x) (hk x hx)]
  · have hex : k ≤ (e x).val := by
      by_contra! h
      have hh : e (e x) = e x := he (e x) h
      have hh' : e x = x := e.injective hh
      rw [hh'] at h
      exact hx h
    rw [hd x (by omega), hd (e x) hex]

/-- In particular, first-use relabellings fixing the nontrivial squaring
cycle preserve the whole prescribed diagonal, including its fixed points. -/
theorem relabel_preserves_square {n : ℕ} (f : Fin n → Fin n → Fin n)
    (d : Fin n → Fin n) (k : ℕ) (hf : ∀ x, f x x = d x)
    (hd : ∀ x, k ≤ x.val → d x = x)
    (hk : ∀ x, x.val < k → (d x).val < k)
    (e : Equiv.Perm (Fin n)) (he : ∀ x, x.val < k → e x = x) :
    ∀ x, relabel f e x x = d x := by
  intro x
  simp only [relabel, hf, commute_of_fixed_initial d k hd hk e he,
    Equiv.apply_symm_apply]

/-- First-use inequalities within the centralizer of a prescribed unary map.
The extra permutation fixes a set of pinned labels. This allows symmetry
breaking for a fixed square map, without silently changing that square map. -/
theorem exists_centralizer_first_use {n m : ℕ} (f : Fin n → Fin n → Fin n)
    (d : Fin n → Fin n) (pins : Finset (Fin n)) (cells : Fin m → Fin n × Fin n) :
    ∃ e : Equiv.Perm (Fin n), (∀ x, e (d x) = d (e x)) ∧
      (∀ x ∈ pins, e x = x) ∧
      ∀ s : Equiv.Perm (Fin n), (∀ x, s (d x) = d (s x)) →
        (∀ x ∈ pins, s x = x) → ∀ i : Fin m,
        (∀ j ≤ i, s (cells j).1 = (cells j).1 ∧ s (cells j).2 = (cells j).2) →
        (∀ j < i, s (relabel f e (cells j).1 (cells j).2) =
          relabel f e (cells j).1 (cells j).2) →
        relabel f e (cells i).1 (cells i).2 ≤ s (relabel f e (cells i).1 (cells i).2) := by
  classical
  let S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter
    (fun e => (∀ x, e (d x) = d (e x)) ∧ ∀ x ∈ pins, e x = x)
  let key (e : Equiv.Perm (Fin n)) : Lex (Fin m → Fin n) :=
    toLex (fun i => relabel f e (cells i).1 (cells i).2)
  obtain ⟨e, he, hmin⟩ := S.exists_min_image key ⟨Equiv.refl _, by simp [S]⟩
  have he' := (Finset.mem_filter.mp he).2
  refine ⟨e, he'.1, he'.2, ?_⟩
  intro s hsd hsp i hin hout
  by_contra! hsmall
  have hnew : e.trans s ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro x
      simp only [Equiv.trans_apply, he'.1, hsd]
    · intro x hx
      simp only [Equiv.trans_apply, he'.2 x hx, hsp x hx]
  have at_cell (j : Fin m) (hj : j ≤ i) :
      relabel f (e.trans s) (cells j).1 (cells j).2 =
        s (relabel f e (cells j).1 (cells j).2) := by
    have h1 : s.symm (cells j).1 = (cells j).1 := by
      apply s.injective
      rw [Equiv.apply_symm_apply, (hin j hj).1]
    have h2 : s.symm (cells j).2 = (cells j).2 := by
      apply s.injective
      rw [Equiv.apply_symm_apply, (hin j hj).2]
    change s (e (f (e.symm (s.symm (cells j).1)) (e.symm (s.symm (cells j).2)))) = _
    rw [h1,h2]
    rfl
  have smaller : key (e.trans s) < key e := by
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      change relabel f (e.trans s) (cells j).1 (cells j).2 =
        relabel f e (cells j).1 (cells j).2
      rw [at_cell j (le_of_lt hj), hout j hj]
    · change relabel f (e.trans s) (cells i).1 (cells i).2 <
        relabel f e (cells i).1 (cells i).2
      rw [at_cell i le_rfl]
      exact hsmall
  exact (not_lt_of_ge (hmin _ hnew)) smaller

end Spectrum.FiniteSearch
