import equational_theories.Spectrum.Equation667883Small.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! A permutation-parity obstruction for commutative E667 magmas.

The permutation sending `y` to the solution of `y ◇ z = x` is
`L_x * L_(x◇x)`. Commutativity makes it an involution. At odd order its
fixed points force squaring to be bijective. At order three modulo four
every such involution is odd, whereas the product of their signs is a square.
No finite search certificate is used. -/

namespace Spectrum.E667.CommutativeParity
noncomputable section
open Equiv
variable {A : Type*} [Magma A] [Fintype A] [DecidableEq A]

def row (h : Equation667 A) (x : A) : Perm A :=
  Equiv.ofBijective (fun y => x ◇ y)
    ⟨E667883.left_injective667 h x,
      Finite.injective_iff_surjective.mp (E667883.left_injective667 h x)⟩

def middle (h : Equation667 A) (x : A) : Perm A := row h x * row h (x ◇ x)

omit [DecidableEq A] in
theorem spec (h : Equation667 A) (x y : A) : y ◇ middle h x y = x :=
  (h x y).symm

omit [DecidableEq A] in
theorem involutive (h : Equation667 A) (hc : ∀ x y : A, x ◇ y = y ◇ x)
    (x : A) : Function.Involutive (middle h x) := by
  intro y
  apply E667883.left_injective667 h (middle h x y)
  exact (spec h x (middle h x y)).trans ((hc _ _).trans (spec h x y)).symm

omit [DecidableEq A] in
theorem fixed_iff (h : Equation667 A) (x y : A) :
    middle h x y = y ↔ y ◇ y = x := by
  constructor
  · intro hy
    simpa only [hy] using spec h x y
  · intro hy
    exact E667883.left_injective667 h y ((spec h x y).trans hy.symm)

theorem square_bijective (h : Equation667 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) (ho : Fintype.card A % 2 = 1) :
    Function.Bijective (fun x : A => x ◇ x) := by
  classical
  suffices hs : Function.Surjective (fun x : A => x ◇ x) from
    ⟨Finite.injective_iff_surjective.mpr hs, hs⟩
  intro x
  let d : Function.End A := fun y => middle h x y
  have hd : d ^ 2 ^ 1 = 1 := by
    funext y
    exact involutive h hc x y
  have hp := Equiv.Perm.card_fixedPoints_modEq hd
  have hn : 0 < Fintype.card d.fixedPoints := by
    change Fintype.card A % 2 = Fintype.card d.fixedPoints % 2 at hp
    omega
  obtain ⟨y⟩ := Fintype.card_pos_iff.mp hn
  exact ⟨y.val, (fixed_iff h x y.val).mp y.property⟩

theorem fixed_card (h : Equation667 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) (ho : Fintype.card A % 2 = 1) (x : A) :
    Fintype.card (Function.fixedPoints (middle h x)) = 1 := by
  classical
  have hb := square_bijective h hc ho
  obtain ⟨a, ha⟩ := hb.2 x
  let e : Function.fixedPoints (middle h x) ≃ Unit := {
    toFun := fun _ => ()
    invFun := fun _ => ⟨a, (fixed_iff h x a).mpr ha⟩
    left_inv := fun y => Subtype.ext
      (hb.1 (((fixed_iff h x y.val).mp y.property).trans ha.symm)).symm
    right_inv := fun _ => rfl }
  simpa using Fintype.card_congr e

theorem not_mod_four_three (h : Equation667 A)
    (hc : ∀ x y : A, x ◇ y = y ◇ x) : Fintype.card A % 4 ≠ 3 := by
  classical
  intro hmod
  have ho : Fintype.card A % 2 = 1 := by omega
  have hb := square_bijective h hc ho
  have hm (x : A) : Perm.sign (middle h x) = -1 := by
    have hp : middle h x ^ 2 = 1 := by
      ext y
      exact involutive h hc x y
    rw [Perm.sign_of_pow_two_eq_one hp, fixed_card h hc ho x]
    exact (Nat.odd_iff.mpr (by omega) : Odd ((Fintype.card A - 1) / 2)).neg_one_pow
  have prod_one : (∏ x : A, Perm.sign (middle h x)) = 1 := by
    simp only [middle, Perm.sign_mul, Finset.prod_mul_distrib]
    rw [hb.prod_comp (fun x => Perm.sign (row h x))]
    exact Int.units_mul_self _
  have prod_neg : (∏ x : A, Perm.sign (middle h x)) = -1 := by
    simp only [hm, Finset.prod_const, Finset.card_univ]
    exact (Nat.odd_iff.mpr ho).neg_one_pow
  have : (1 : ℤˣ) = -1 := prod_one.symm.trans prod_neg
  norm_num at this

end
end Spectrum.E667.CommutativeParity

namespace Spectrum.E667
/-- Every commutative finite E667 magma has order other than three modulo four. -/
theorem not_commutative_of_card_mod_four_three {A : Type*} [Magma A] [Finite A]
    (h : Equation667 A) (hn : Nat.card A % 4 = 3) :
    ¬ ∀ x y : A, x ◇ y = y ◇ x := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  intro hc
  exact CommutativeParity.not_mod_four_three h hc
    (by simpa only [Nat.card_eq_fintype_card] using hn)

spectrum_assert not_commutative_of_card_mod_four_three complete
end Spectrum.E667
