import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Conj

/-! Name a bounded tuple of distinct points before applying symmetry breaking. -/
namespace Spectrum.FiniteSearch

theorem exists_perm_initial {k n : ℕ} (hk : k ≤ n) (f : Fin k → Fin n)
    (hi : Function.Injective f) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, e (f i) = i.castLE hk := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun x => x.val < k)
  let g : Fin n → Fin n := fun x => if h : x.val < k then f ⟨x.val,h⟩ else x
  have hgi : Set.InjOn g s := by
    intro a ha b hb he
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    simp only [g,dif_pos ha',dif_pos hb'] at he
    exact Fin.ext (congrArg (fun t : Fin k => t.val) (hi he))
  obtain ⟨e,he⟩ := Finset.exists_equiv_extend_of_card_eq
    (t := Finset.univ (α := Fin n)) (by simp) (f := g) (by simp) hgi
  let E : Equiv.Perm (Fin n) := Equiv.ofBijective (fun x => (e x).val) ⟨
    fun _ _ h => e.injective (Subtype.ext h),
    fun y => by
      obtain ⟨x,hx⟩ := e.surjective ⟨y,Finset.mem_univ _⟩
      exact ⟨x,congrArg Subtype.val hx⟩⟩
  refine ⟨E.symm, ?_⟩
  intro i
  apply E.injective
  rw [Equiv.apply_symm_apply]
  have hm : i.castLE hk ∈ s := by simp [s]
  have hh := he (i.castLE hk) hm
  change f i = (e (i.castLE hk)).val
  simpa [g] using hh.symm

/-- Conjugate permutations fixing a distinguished point can be conjugated
by a permutation that also fixes that point. -/
theorem conjugate_fix_point {A : Type*} [DecidableEq A]
    (f g : Equiv.Perm A) (a : A) (hf : f a = a) (hg : g a = a)
    (h : IsConj f g) :
    ∃ e : Equiv.Perm A, e a = a ∧ ∀ x, e (f (e.symm x)) = g x := by
  obtain ⟨e,he⟩ := isConj_iff.mp h
  have hh (x : A) : e (f (e.symm x)) = g x :=
    congrArg (fun p : Equiv.Perm A => p x) he
  have hx : g (e a) = e a := by
    rw [← hh]
    simp [hf]
  let s := Equiv.swap (e a) a
  have hc : g * s = s * g := by
    simpa only [hx,hg] using Equiv.mul_swap_eq_swap_mul g (e a) a
  refine ⟨e.trans s, ?_, ?_⟩
  · simp [s]
  · intro x
    change s (e (f (e.symm (s x)))) = g x
    rw [hh]
    have hcx := congrArg (fun p : Equiv.Perm A => p (s x)) hc
    simpa [s] using hcx.symm

end Spectrum.FiniteSearch
