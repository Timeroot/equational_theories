import equational_theories.Parastrophes.FiniteInverseFamily
import equational_theories.Equations.All

/-! A limitation of extending a magma by finitely many new rows. For E1075
and E1278, if products remain in the block of their right argument, every new
row restricted to the old block must be bijective. -/
namespace Parastrophes.FiniteBlockExtensions

@[implicit_reducible] def magma {G I : Type*}
    (old : G → G → G) (new : I → I → I)
    (f : I → G → G) (r : G → I → I) : Magma (Sum G I) where
  op
  | .inl x, .inl y => .inl (old x y)
  | .inl x, .inr i => .inr (r x i)
  | .inr i, .inl x => .inl (f i x)
  | .inr i, .inr j => .inr (new i j)

variable {G I : Type*} [Finite I]
variable (old : G → G → G) (new : I → I → I)
variable (f : I → G → G) (r : G → I → I)

theorem new_rows1075 (h : @Equation1075 _ (magma old new f r)) :
    ∀ i, Function.Bijective (f i) := by
  have hr (x : G) : Function.Bijective (r x) := by
    have hs : Function.Surjective (r x) := by
      intro i
      refine ⟨r (f i (f i x)) i, ?_⟩
      exact (Sum.inr.inj (h (.inr i) (.inl x))).symm
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  let e (x : G) : Equiv.Perm I := Equiv.ofBijective (r x) (hr x)
  apply finite_inverse_family f (fun x => (e x).trans (e x))
  intro i x
  exact (Sum.inl.inj (h (.inl x) (.inr i))).symm

theorem new_rows1278 (h : @Equation1278 _ (magma old new f r)) :
    ∀ i, Function.Bijective (f i) := by
  have hr (x : G) : Function.Bijective (r x) := by
    have hs : Function.Surjective (r x) := by
      intro i
      refine ⟨r (f (new i i) x) i, ?_⟩
      exact (Sum.inr.inj (h (.inr i) (.inl x))).symm
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  let e (x : G) : Equiv.Perm I := Equiv.ofBijective (r (old x x)) (hr (old x x))
  apply finite_inverse_family f e
  intro i x
  exact (Sum.inl.inj (h (.inl x) (.inr i))).symm

end Parastrophes.FiniteBlockExtensions
