import equational_theories.Parastrophes.Equation115BooleanTurn
import Mathlib.Data.ZMod.Basic

/-! Finite additive quotients preserve any prescribed finite collection of
points in the integer group used by the E115 triangle construction. -/
namespace Parastrophes.Eq115BooleanTurn
noncomputable section

private theorem coordinate_separates (x : W) (hx : x≠0) :
    ∃ f : W →+ ℤ, f x ≠ 0 := by
  classical
  by_cases hh : x.1=0
  · by_cases hp : x.2.1=0
    · have hr : x.2.2 ≠ 0 := by
        intro hr
        exact hx (Prod.ext hh (Prod.ext hp hr))
      have hex : ∃ k, x.2.2 k ≠ 0 := by
        by_contra! he
        exact hr (Finsupp.ext he)
      obtain ⟨k,hk⟩ := hex
      exact ⟨{ toFun := fun y => y.2.2 k, map_zero' := rfl, map_add' := fun _ _ => rfl },hk⟩
    · have hex : ∃ k, x.2.1 k ≠ 0 := by
        by_contra! he
        exact hp (Finsupp.ext he)
      obtain ⟨k,hk⟩ := hex
      exact ⟨{ toFun := fun y => y.2.1 k, map_zero' := rfl, map_add' := fun _ _ => rfl },hk⟩
  · exact ⟨{ toFun := Prod.fst, map_zero' := rfl, map_add' := fun _ _ => rfl },hh⟩

private theorem cast_nonzero (z : ℤ) (hz : z≠0) :
    (z : ZMod (z.natAbs+1)) ≠ 0 := by
  intro he
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd z _).mp he
  have hn := Int.natCast_dvd.mp hd
  have hp : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  have hh := Nat.le_of_dvd hp hn
  omega

/-- The finite group is a product of cyclic groups, one separating coordinate
for each distinct pair of selected points. No quantitative bound is needed. -/
theorem finite_separation (S : Finset W) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Finite V) (f : W →+ V),
      Set.InjOn f (↑S : Set W) := by
  classical
  let P := S × S
  have hex (p : P) : ∃ f : W →+ ℤ, p.1.val ≠ p.2.val → f (p.1.val-p.2.val) ≠ 0 := by
    by_cases h : p.1.val=p.2.val
    · exact ⟨0,fun hn => False.elim (hn h)⟩
    · obtain ⟨f,hf⟩ := coordinate_separates (p.1.val-p.2.val) (sub_ne_zero.mpr h)
      exact ⟨f,fun _ => hf⟩
  choose g hg using hex
  let n (p : P) := (g p (p.1.val-p.2.val)).natAbs+1
  letI (p : P) : NeZero (n p) := ⟨by dsimp [n]; omega⟩
  let V := (p : P) → ZMod (n p)
  let f : W →+ V :=
    { toFun := fun x p => (g p x : ZMod (n p)),
      map_zero' := by funext p; change (g p 0 : ZMod (n p))=0; simp,
      map_add' := by
        intro x y; funext p
        change (g p (x+y) : ZMod (n p))=(g p x : ZMod (n p))+(g p y : ZMod (n p))
        simp }
  refine ⟨V,inferInstance,inferInstance,f,?_⟩
  intro x hx y hy he
  by_contra hn
  let p : P := (⟨x,hx⟩,⟨y,hy⟩)
  have hp := congrFun he p
  have hz : (g p (x-y) : ZMod (n p))=0 := by
    change (g p x : ZMod (n p))=(g p y : ZMod (n p)) at hp
    rw [map_sub,Int.cast_sub,hp,sub_self]
  exact cast_nonzero (g p (x-y)) (hg p hn) hz

end
end Parastrophes.Eq115BooleanTurn
