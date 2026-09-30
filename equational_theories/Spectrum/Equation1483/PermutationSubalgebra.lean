import equational_theories.Spectrum.Equation1483.PermutationCover
import equational_theories.Spectrum.Equation1483.ConstantSpectrum
import equational_theories.Spectrum.WeakCentral.Dyadic
import Mathlib.Data.Fintype.Sigma

/-! Subalgebras of the permutation-cover construction have rectangular fibers.
If the projected subalgebra has a constant row, its order is a square times a
power of two. No general E1483 representation theorem is assumed. -/
namespace Spectrum.E1483.PermutationCover

variable {G K S : Type*} (f : G → G → G)
  (a b : G → G → K) (p : K → S ≃ S)

abbrev Closed (H : Set (G × S × S)) : Prop :=
  ∀ X ∈ H, ∀ Y ∈ H, extension f a b p X Y ∈ H

abbrev Base (H : Set (G × S × S)) := {x : G // ∃ u v, (x, u, v) ∈ H}
abbrev LeftFiber (H : Set (G × S × S)) (x : G) := {u : S // ∃ v, (x, u, v) ∈ H}
abbrev RightFiber (H : Set (G × S × S)) (x : G) := {v : S // ∃ u, (x, u, v) ∈ H}

variable {f a b p}

/-- The E1483 word splices the two coordinates of points with the same base. -/
theorem splice
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X)
    {H : Set (G × S × S)} (hH : Closed f a b p H)
    {x : G} {u v u' v' : S} (h₁ : (x, u, v') ∈ H) (h₂ : (x, u', v) ∈ H) :
    (x, u, v) ∈ H := by
  have hm := hH _ (hH _ h₁ _ h₁) _ (hH _ h₂ _ (hH _ h₁ _ h₁))
  have he := h (x, u, v) (x, u, v') (x, u, v')
  change extension f a b p (extension f a b p (x, u, v') (x, u, v))
    (extension f a b p (x, u, v) (extension f a b p (x, u, v') (x, u, v'))) =
    (x, u, v) at he
  simpa only [extension] using he ▸ hm

/-- Exact rectangular coordinates for each fiber, with no finiteness assumption. -/
def subalgebraEquiv
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X)
    {H : Set (G × S × S)} (hH : Closed f a b p H) :
    H ≃ ((x : Base H) × (LeftFiber H x.val × RightFiber H x.val)) where
  toFun X := ⟨⟨X.val.1, X.val.2.1, X.val.2.2, X.property⟩,
    ⟨⟨X.val.2.1, X.val.2.2, X.property⟩, ⟨X.val.2.2, X.val.2.1, X.property⟩⟩⟩
  invFun X := ⟨(X.1.val, X.2.1.val, X.2.2.val), by
    obtain ⟨v, hv⟩ := X.2.1.property
    obtain ⟨u, hu⟩ := X.2.2.property
    exact splice h hH hv hu⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem right_le_left [Finite S] {H : Set (G × S × S)}
    (hH : Closed f a b p H) (x y : Base H) :
    Nat.card (RightFiber H x.val) ≤ Nat.card (LeftFiber H (f x.val y.val)) := by
  obtain ⟨s, t, hy⟩ := y.property
  let g : RightFiber H x.val → LeftFiber H (f x.val y.val) := fun v =>
    ⟨(p (b x.val y.val)).symm v.val, by
      obtain ⟨u, hu⟩ := v.property
      exact ⟨p (a x.val y.val) s, hH _ hu _ hy⟩⟩
  apply Nat.card_le_card_of_injective g
  intro v w he
  apply Subtype.ext
  exact (p (b x.val y.val)).symm.injective (congrArg Subtype.val he)

private theorem left_le_right [Finite S] {H : Set (G × S × S)}
    (hH : Closed f a b p H) (x y : Base H) :
    Nat.card (LeftFiber H y.val) ≤ Nat.card (RightFiber H (f x.val y.val)) := by
  obtain ⟨u, v, hx⟩ := x.property
  let g : LeftFiber H y.val → RightFiber H (f x.val y.val) := fun s =>
    ⟨p (a x.val y.val) s.val, by
      obtain ⟨t, ht⟩ := s.property
      exact ⟨(p (b x.val y.val)).symm v, hH _ hx _ ht⟩⟩
  apply Nat.card_le_card_of_injective g
  intro s t he
  apply Subtype.ext
  exact (p (a x.val y.val)).injective (congrArg Subtype.val he)

/-- The projected points are a subalgebra of the base. -/
@[implicit_reducible] def baseMagma {H : Set (G × S × S)} (hH : Closed f a b p H) : Magma (Base H) where
  op x y := ⟨f x.val y.val, by
    obtain ⟨u, v, hx⟩ := x.property
    obtain ⟨s, t, hy⟩ := y.property
    exact ⟨(p (b x.val y.val)).symm v, p (a x.val y.val) s, hH _ hx _ hy⟩⟩

theorem base_lawful {H : Set (G × S × S)} (hH : Closed f a b p H)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x) :
    @Equation1483 (Base H) (baseMagma hH) := by
  intro x y z
  exact Subtype.ext (hf x.val y.val z.val).symm

/-- Finite fiber sizes form a homomorphism to a natural central groupoid. -/
theorem fiber_sizes [Finite S] {H : Set (G × S × S)}
    (hH : Closed f a b p H)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x) (x y : Base H) :
    Nat.card (LeftFiber H (f x.val y.val)) = Nat.card (RightFiber H x.val) ∧
    Nat.card (RightFiber H (f x.val y.val)) = Nat.card (LeftFiber H y.val) := by
  letI := baseMagma hH
  have he := base_lawful hH hf
  have hl := right_le_left hH x y
  have hr := left_le_right hH x y
  have hl' := left_le_right hH ((x ◇ y) ◇ x) (x ◇ y)
  have hr' := right_le_left hH (x ◇ y) (y ◇ (x ◇ x))
  have hd := CentralDual.dual he x y x
  have hh := he y x x
  change _ ≤ Nat.card (RightFiber H (((x ◇ y) ◇ x) ◇ (x ◇ y)).val) at hl'
  change _ ≤ Nat.card (LeftFiber H ((x ◇ y) ◇ (y ◇ (x ◇ x))).val) at hr'
  rw [hd] at hl'
  rw [← hh] at hr'
  exact ⟨Nat.le_antisymm hl' hl, Nat.le_antisymm hr' hr⟩

/-- A constant row in the projected subalgebra forces equally sized square fibers. -/
theorem card_of_constant_base [Finite G] [Finite S] {H : Set (G × S × S)}
    (hH : Closed f a b p H)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X)
    (zero one : Base H) (hz : ∀ y : Base H, f zero.val y.val = one.val) :
    ∃ k s : ℕ, Nat.card H = 2 ^ k * s ^ 2 := by
  classical
  letI := baseMagma hH
  have he := base_lawful hH hf
  have hz' : ∀ y : Base H, zero ◇ y = one := fun y => Subtype.ext (hz y)
  obtain ⟨k, hk⟩ := Constant.card_pow_two he zero one hz'
  let s := Nat.card (RightFiber H one.val)
  have hu (y : Base H) : Nat.card (LeftFiber H y.val) = s := by
    have hy := (fiber_sizes hH hf zero y).2
    rw [hz y] at hy
    exact hy.symm
  have hv (y : Base H) : Nat.card (RightFiber H y.val) = s := by
    have hy := (fiber_sizes hH hf y zero).1
    exact hy.symm.trans (hu (y ◇ zero))
  refine ⟨k, s, ?_⟩
  rw [Nat.card_congr (subalgebraEquiv h hH)]
  letI := Fintype.ofFinite (Base H)
  rw [Nat.card_sigma]
  simp only [Nat.card_prod, hu, hv, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hk, pow_two]

/-- Consequently this construction cannot produce a new order from such a base,
even by taking an arbitrary subalgebra. -/
theorem square_or_twice_square_of_constant_base [Finite G] [Finite S]
    {H : Set (G × S × S)} (hH : Closed f a b p H)
    (hf : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (h : ∀ X Y Z, extension f a b p (extension f a b p Y X)
      (extension f a b p X (extension f a b p Y Z)) = X)
    (zero one : Base H) (hz : ∀ y : Base H, f zero.val y.val = one.val) :
    ∃ r : ℕ, Nat.card H = r ^ 2 ∨ Nat.card H = 2 * r ^ 2 := by
  obtain ⟨k, s, hs⟩ := card_of_constant_base hH hf h zero one hz
  apply WeakCentralGroupoid.square_or_twice_square_of_dyadic
  simpa only [Nat.mul_comm] using hs

/-- info: 'Spectrum.E1483.PermutationCover.splice' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splice
/-- info: 'Spectrum.E1483.PermutationCover.fiber_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fiber_sizes
/-- info: 'Spectrum.E1483.PermutationCover.square_or_twice_square_of_constant_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms square_or_twice_square_of_constant_base

end Spectrum.E1483.PermutationCover
