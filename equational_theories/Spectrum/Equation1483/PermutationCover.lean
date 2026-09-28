import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Equiv.Basic

/-! General E1483 constructions from permutation data and covers of natural
central groupoids. Triangle permutations give central models with arbitrary
label-fiber sizes. The extension construction permits an arbitrary E1483 base.
See docs/1483_general_constructions.md. -/

namespace Spectrum.E1483.PermutationCover

section Triangles
variable {I : Type*} {S : I → Type*}
  (p : (i j k : I) → S j ≃ S j)

abbrev Point (S : I → Type*) := Σ i, S i

def triangle (x y : Point S × Point S) : Point S × Point S :=
  (⟨x.2.1, (p x.1.1 x.2.1 y.1.1).symm x.2.2⟩,
   ⟨y.1.1, p x.2.1 y.1.1 y.2.1 y.1.2⟩)

/-- Arbitrary permutations on triples of labels give a central groupoid. -/
theorem triangle_central (x y z : Point S × Point S) :
    triangle p (triangle p y x) (triangle p x z) = x := by
  rcases x with ⟨⟨i, a⟩, ⟨j, b⟩⟩
  rcases y with ⟨⟨k, c⟩, ⟨l, d⟩⟩
  rcases z with ⟨⟨m, e⟩, ⟨n, f⟩⟩
  dsimp only [triangle]
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The same family satisfies E1483. -/
theorem triangle_lawful (x y z : Point S × Point S) :
    triangle p (triangle p y x) (triangle p x (triangle p y z)) = x :=
  triangle_central p x y (triangle p y z)

/-- Label sets may have different sizes. -/
theorem triangle_card [Fintype I] [∀ i, Fintype (S i)] :
    Fintype.card (Point S × Point S) = (∑ i, Fintype.card (S i)) ^ 2 := by
  simp only [Point, Fintype.card_prod, Fintype.card_sigma, pow_two]
end Triangles

section Extension
variable {G K S : Type*} (f : G → G → G)
  (a b : G → G → K) (p : K → S ≃ S)

def extension (x y : G × S × S) : G × S × S :=
  (f x.1 y.1, (p (b x.1 y.1)).symm x.2.2, p (a x.1 y.1) y.2.1)

/-- Color the coefficient positions by connected components of the two displayed
relations. Every independent choice of a permutation for each color then gives
an E1483 extension, multiplying the order by a square. -/
theorem extension_lawful
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (ha : ∀ x y z, b (f y x) (f x (f y z)) = a y x)
    (hb : ∀ x y z, a (f y x) (f x (f y z)) = b x (f y z))
    (x y z : G × S × S) :
    extension f a b p (extension f a b p y x)
      (extension f a b p x (extension f a b p y z)) = x := by
  rcases x with ⟨x, u, v⟩
  simp only [extension, h, ha, hb, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

theorem extension_card [Fintype G] [Fintype S] :
    Fintype.card (G × S × S) = Fintype.card G * Fintype.card S ^ 2 := by
  simp only [Fintype.card_prod, pow_two]
end Extension

section Weighted
variable {G I J : Type*} (f : G → G → G) (l r : G → I) (label : J → I)

def Weighted := {x : G × J × J // l x.1 = label x.2.1 ∧ r x.1 = label x.2.2}

def weighted (hl : ∀ x y, l (f x y) = r x) (hr : ∀ x y, r (f x y) = l y)
    (x y : Weighted l r label) : Weighted l r label :=
  ⟨(f x.val.1 y.val.1, x.val.2.2, y.val.2.1),
    (hl _ _).trans x.property.2, (hr _ _).trans y.property.1⟩

theorem weighted_lawful
    (hl : ∀ x y, l (f x y) = r x) (hr : ∀ x y, r (f x y) = l y)
    (h : ∀ x y z, f (f y x) (f x (f y z)) = x)
    (x y z : Weighted l r label) :
    weighted f l r label hl hr (weighted f l r label hl hr y x)
      (weighted f l r label hl hr x (weighted f l r label hl hr y z)) = x := by
  apply Subtype.ext
  exact Prod.ext (h _ _ _) rfl
end Weighted

/-- info: 'Spectrum.E1483.PermutationCover.triangle_central' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms triangle_central
/-- info: 'Spectrum.E1483.PermutationCover.extension_lawful' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms extension_lawful
/-- info: 'Spectrum.E1483.PermutationCover.weighted_lawful' does not depend on any axioms -/
#guard_msgs in
#print axioms weighted_lawful
end Spectrum.E1483.PermutationCover
