import equational_theories.Spectrum.Equation1483.ConstantDefinability
import equational_theories.Spectrum.Equation1483.PermutationCover
import Mathlib.Data.Finite.Card

/-! Intrinsic recognition of the minimum-rank fiber in a permutation cover.
These lemmas are general in the finite base and the permutation degree. -/
namespace Spectrum.E1483.PermutationDefinability

variable (G S : Type) [Magma G]

structure Data where
  A : G → G → S ≃ S
  B : G → G → S ≃ S
  zero : G
  one : G
  law : Equation1483 G
  constant : ∀ x, zero ◇ x = one
  cancel₁ : ∀ x y z, B (y ◇ x) (x ◇ (y ◇ z)) = A y x
  cancel₂ : ∀ x y z, A (y ◇ x) (x ◇ (y ◇ z)) = B x (y ◇ z)

abbrev Point := G × S × S
variable {G S} (D : Data G S)

namespace Data

def operation (X Y : Point G S) : Point G S :=
  (X.1 ◇ Y.1, (D.B X.1 Y.1).symm X.2.2, D.A X.1 Y.1 Y.2.1)

@[implicit_reducible] def magma : Magma (Point G S) := ⟨D.operation⟩

theorem lawful (X Y Z : Point G S) :
    D.operation (D.operation Y X) (D.operation X (D.operation Y Z)) = X := by
  rcases X with ⟨x, u, v⟩
  simp only [operation, ← D.law, D.cancel₁, D.cancel₂,
    Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem column (x : G) : x ◇ D.zero = D.one :=
  Constant.constant_column D.law D.zero D.one D.constant x

theorem left_inverse (x : G) : D.one ◇ (x ◇ D.one) = x :=
  Constant.left_inverse D.law D.zero D.one D.constant x

theorem right_inverse (x : G) : (D.one ◇ x) ◇ D.one = x :=
  Constant.right_inverse D.law D.zero D.one D.constant x

theorem B_zero (y : G) : D.B D.zero y = D.A D.one D.one := by
  have he := D.cancel₂ D.zero (D.one ◇ y) D.one
  simpa only [D.column, D.constant, D.right_inverse] using he.symm

abbrev Row (X : Point G S) := {Y : Point G S // ∃ Z, D.operation X Z = Y}
abbrev BaseRow (x : G) := {y : G // ∃ z, x ◇ z = y}

def zeroRowEquiv (u v : S) : D.Row (D.zero, u, v) ≃ S where
  toFun Y := Y.val.2.2
  invFun s := ⟨(D.one, (D.A D.one D.one).symm v, s),
    (D.zero, (D.A D.zero D.zero).symm s, v), by
      simp only [operation, D.constant, D.B_zero, Equiv.apply_symm_apply]⟩
  left_inv Y := by
    apply Subtype.ext
    obtain ⟨Z, hZ⟩ := Y.property
    change (D.one, (D.A D.one D.one).symm v, Y.val.2.2) = Y.val
    rw [← hZ]
    simp only [operation, D.constant, D.B_zero]
  right_inv _ := rfl

theorem zero_row_card (u v : S) : Nat.card (D.Row (D.zero, u, v)) = Nat.card S :=
  Nat.card_congr (D.zeroRowEquiv u v)

/-- Each distinct base output contributes a disjoint copy of the fiber set. -/
theorem row_lower [Finite G] [Finite S] (X : Point G S) :
    Nat.card (BaseRow X.1) * Nat.card S ≤ Nat.card (D.Row X) := by
  classical
  let g : BaseRow X.1 × S → D.Row X := fun z =>
    ⟨(z.1.val, (D.B X.1 z.1.property.choose).symm X.2.2, z.2),
      (z.1.property.choose, (D.A X.1 z.1.property.choose).symm z.2, X.2.2), by
        simp only [operation, z.1.property.choose_spec, Equiv.apply_symm_apply]⟩
  have hi : Function.Injective g := by
    intro z w he
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun Y : D.Row X => Y.val.1) he)
    · exact congrArg (fun Y : D.Row X => Y.val.2.2) he
  have hc := Nat.card_le_card_of_injective g hi
  simpa only [Nat.card_prod] using hc

/-- Minimum row rank identifies the entire zero fiber intrinsically. -/
theorem zero_of_small_row [Finite G] [Finite S] [Nonempty S] (X : Point G S)
    (hc : Nat.card (D.Row X) ≤ Nat.card S) : X.1 = D.zero := by
  have hp : 0 < Nat.card S := Nat.card_pos
  have hl := (D.row_lower X).trans hc
  have hb : Nat.card (BaseRow X.1) ≤ 1 := by nlinarith
  letI : Subsingleton (BaseRow X.1) := Finite.card_le_one_iff_subsingleton.mp hb
  apply Constant.constant_row_unique D.law D.zero D.one D.constant X.1 (X.1 ◇ D.zero)
  intro y
  exact congrArg Subtype.val (Subsingleton.elim
    (⟨X.1 ◇ y, y, rfl⟩ : BaseRow X.1) ⟨X.1 ◇ D.zero, D.zero, rfl⟩)

/-- Row images are transported bijectively by source automorphisms. -/
theorem row_card_map (F : Point G S → Point G S) (hbij : Function.Bijective F)
    (hhom : ∀ X Y, F (D.operation X Y) = D.operation (F X) (F Y)) (X : Point G S) :
    Nat.card (D.Row (F X)) = Nat.card (D.Row X) := by
  let g : D.Row X → D.Row (F X) := fun Y => ⟨F Y.val, by
    obtain ⟨Z, hZ⟩ := Y.property
    exact ⟨F Z, (hhom X Z).symm.trans (congrArg F hZ)⟩⟩
  have hi : Function.Injective g := by
    intro Y Z he
    exact Subtype.ext (hbij.1 (congrArg Subtype.val he))
  have hs : Function.Surjective g := by
    intro Y
    obtain ⟨Z, hz⟩ := Y.property
    obtain ⟨W, hw⟩ := hbij.2 Z
    refine ⟨⟨D.operation X W, W, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (hhom X W).trans (by rw [hw, hz])
  exact (Nat.card_congr (Equiv.ofBijective g ⟨hi, hs⟩)).symm

theorem map_zero [Finite G] [Finite S] [Nonempty S]
    (F : Point G S → Point G S) (hbij : Function.Bijective F)
    (hhom : ∀ X Y, F (D.operation X Y) = D.operation (F X) (F Y)) (u v : S) :
    (F (D.zero, u, v)).1 = D.zero := by
  apply D.zero_of_small_row
  rw [D.row_card_map F hbij hhom, D.zero_row_card]

end Data
end Spectrum.E1483.PermutationDefinability
