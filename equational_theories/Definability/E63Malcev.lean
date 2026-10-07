import equational_theories.Definability.E63Family
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Mal'tsev terms throughout the E63 family

One-sided division identities already suffice for a Mal'tsev term. In particular,
E73 and E118 have such terms without any finiteness or cancellation assumption.
The known term operations transfer this to E63 and E1692. Thus an asymmetric
reflexive compatible relation cannot separate any of these laws from E125.
-/

namespace E63Family

variable {G : Type*} [M : Magma G]

/-- Only two of the four quasigroup division identities are required. -/
structure SplitDivisions where
  leftDiv : G → G → G
  rightDiv : G → G → G
  mul_leftDiv : ∀ x y, x ◇ leftDiv x y = y
  rightDiv_mul : ∀ x y, rightDiv (x ◇ y) y = x

namespace SplitDivisions

variable (d : SplitDivisions (G := G))

/-- A Mal'tsev operation from a right inverse of each left translation and
a left inverse of each right translation. If the divisions are terms, so is this. -/
def malcev (x y z : G) : G :=
  d.rightDiv (z ◇ d.leftDiv y x) (d.leftDiv x x)

theorem malcev_left (x y : G) : d.malcev x y y = x := by
  simp only [malcev, d.mul_leftDiv]
  calc
    d.rightDiv x (d.leftDiv x x) =
        d.rightDiv (x ◇ d.leftDiv x x) (d.leftDiv x x) := by rw [d.mul_leftDiv]
    _ = x := d.rightDiv_mul x _

theorem malcev_right (y z : G) : d.malcev y y z = z := d.rightDiv_mul z _

include d in
theorem right_injective (y : G) : Function.Injective (fun x => x ◇ y) :=
  (show Function.LeftInverse (fun x => d.rightDiv x y) (fun x => x ◇ y) from
    fun x => d.rightDiv_mul x y).injective

/-- This injection sends `a` to `b`, and has a term left inverse whenever the
divisions are terms. Surjectivity does not follow from the split identities. -/
def transport (a b x : G) : G := x ◇ d.leftDiv a b

def retract (a b x : G) : G := d.rightDiv x (d.leftDiv a b)

theorem transport_base (a b : G) : d.transport a b a = b := d.mul_leftDiv a b

theorem retract_transport (a b x : G) : d.retract a b (d.transport a b x) = x :=
  d.rightDiv_mul x _

theorem transport_injective (a b : G) : Function.Injective (d.transport a b) :=
  (show Function.LeftInverse (d.retract a b) (d.transport a b) from
    d.retract_transport a b).injective

end SplitDivisions

def split73 (h : Equation73 G) : SplitDivisions (G := G) where
  leftDiv x y := x ◇ (y ◇ x)
  rightDiv x y := y ◇ (y ◇ x)
  mul_leftDiv x y := (h y x).symm
  rightDiv_mul x y := (h x y).symm

def split118 (h : Equation118 G) : SplitDivisions (G := G) where
  leftDiv x y := (y ◇ x) ◇ x
  rightDiv x y := y ◇ (x ◇ y)
  mul_leftDiv x y := (h y x).symm
  rightDiv_mul x y := (h x y).symm

/-- E73 Mal'tsev term: `s * (s * (z * (y * (x*y)))))`, where `s=x*(x*x)`. -/
def malcev73 (x y z : G) : G :=
  let s := x ◇ (x ◇ x)
  s ◇ (s ◇ (z ◇ (y ◇ (x ◇ y))))

theorem malcev73_left (h : Equation73 G) (x y : G) : malcev73 x y y = x :=
  (split73 h).malcev_left x y

theorem malcev73_right (h : Equation73 G) (y z : G) : malcev73 y y z = z :=
  (split73 h).malcev_right y z

/-- E118 Mal'tsev term: `s * ((z * ((x*y)*y)) * s)`, where `s=(x*x)*x`. -/
def malcev118 (x y z : G) : G :=
  let s := (x ◇ x) ◇ x
  s ◇ ((z ◇ ((x ◇ y) ◇ y)) ◇ s)

theorem malcev118_left (h : Equation118 G) (x y : G) : malcev118 x y y = x :=
  (split118 h).malcev_left x y

theorem malcev118_right (h : Equation118 G) (y z : G) : malcev118 y y z = z :=
  (split118 h).malcev_right y z

@[reducible] def companion63 : Magma G := ⟨fun x y => x ◇ (x ◇ y)⟩

theorem companion63_equation118 (h : Equation63 G) : @Equation118 G companion63 := by
  intro x y
  change x = y ◇ (y ◇ ((x ◇ (x ◇ y)) ◇ ((x ◇ (x ◇ y)) ◇ y)))
  rw [← h (x ◇ (x ◇ y)) y]
  exact h x y

@[reducible] def companion1692 : Magma G := ⟨fun x y => y ◇ (y ◇ x)⟩

theorem companion1692_equation73 (h : Equation1692 G) : @Equation73 G companion1692 := by
  intro x y
  change x = ((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y)) ◇
    (((y ◇ (y ◇ x)) ◇ ((y ◇ (y ◇ x)) ◇ y)) ◇ y)
  rw [← h (y ◇ x) y]
  exact h x y

def malcev63 (x y z : G) : G := @malcev118 G companion63 x y z

theorem malcev63_left (h : Equation63 G) (x y : G) : malcev63 x y y = x :=
  @malcev118_left G companion63 (companion63_equation118 h) x y

theorem malcev63_right (h : Equation63 G) (y z : G) : malcev63 y y z = z :=
  @malcev118_right G companion63 (companion63_equation118 h) y z

def malcev1692 (x y z : G) : G := @malcev73 G companion1692 x y z

theorem malcev1692_left (h : Equation1692 G) (x y : G) : malcev1692 x y y = x :=
  @malcev73_left G companion1692 (companion1692_equation73 h) x y

theorem malcev1692_right (h : Equation1692 G) (y z : G) : malcev1692 y y z = z :=
  @malcev73_right G companion1692 (companion1692_equation73 h) y z

/-- Preservation of a binary relation by a binary operation. -/
def Respects₂ (f : G → G → G) (R : G → G → Prop) : Prop :=
  ∀ ⦃x x' y y'⦄, R x x' → R y y' → R (f x y) (f x' y')

def Compatible (R : G → G → Prop) : Prop := Respects₂ (· ◇ ·) R

/-- A split-division presentation whose three operations preserve every source
compatible relation. Our examples use explicit source terms for all three. -/
structure SplitPresentation where
  magma : Magma G
  divisions : @SplitDivisions G magma
  mul_compatible : ∀ R, @Compatible G M R → @Compatible G magma R
  leftDiv_compatible : ∀ R, @Compatible G M R → Respects₂ divisions.leftDiv R
  rightDiv_compatible : ∀ R, @Compatible G M R → Respects₂ divisions.rightDiv R

def presentation73 (h : Equation73 G) : SplitPresentation (G := G) where
  magma := inferInstance
  divisions := split73 h
  mul_compatible _ hc := hc
  leftDiv_compatible _ hc _ _ _ _ h1 h2 := hc h1 (hc h2 h1)
  rightDiv_compatible _ hc _ _ _ _ h1 h2 := hc h2 (hc h2 h1)

def presentation118 (h : Equation118 G) : SplitPresentation (G := G) where
  magma := inferInstance
  divisions := split118 h
  mul_compatible _ hc := hc
  leftDiv_compatible _ hc _ _ _ _ h1 h2 := hc (hc h2 h1) h1
  rightDiv_compatible _ hc _ _ _ _ h1 h2 := hc h2 (hc h1 h2)

def presentation63 (h : Equation63 G) : SplitPresentation (G := G) where
  magma := companion63
  divisions := @split118 G companion63 (companion63_equation118 h)
  mul_compatible _ hc _ _ _ _ h1 h2 := hc h1 (hc h1 h2)
  leftDiv_compatible R hc := by
    have hq : @Compatible G companion63 R := fun {_ _ _ _} h1 h2 => hc h1 (hc h1 h2)
    intro x x' y y' hx hy
    exact hq (hq hy hx) hx
  rightDiv_compatible R hc := by
    have hq : @Compatible G companion63 R := fun {_ _ _ _} h1 h2 => hc h1 (hc h1 h2)
    intro x x' y y' hx hy
    exact hq hy (hq hx hy)

def presentation1692 (h : Equation1692 G) : SplitPresentation (G := G) where
  magma := companion1692
  divisions := @split73 G companion1692 (companion1692_equation73 h)
  mul_compatible _ hc _ _ _ _ h1 h2 := hc h2 (hc h2 h1)
  leftDiv_compatible R hc := by
    have hq : @Compatible G companion1692 R := fun {_ _ _ _} h1 h2 => hc h2 (hc h2 h1)
    intro x x' y y' hx hy
    exact hq hx (hq hy hx)
  rightDiv_compatible R hc := by
    have hq : @Compatible G companion1692 R := fun {_ _ _ _} h1 h2 => hc h2 (hc h2 h1)
    intro x x' y y' hx hy
    exact hq hy (hq hy hx)

theorem exists_splitPresentation
    (h : Equation63 G ∨ Equation73 G ∨ Equation118 G ∨ Equation125 G ∨ Equation1692 G) :
    Nonempty (SplitPresentation (G := G)) := by
  rcases h with h | h | h | h | h
  · exact ⟨presentation63 h⟩
  · exact ⟨presentation73 h⟩
  · exact ⟨presentation118 h⟩
  · exact ⟨presentation73 (equation73_of_125 h)⟩
  · exact ⟨presentation1692 h⟩

namespace SplitPresentation
variable (P : SplitPresentation (G := G))
include P

theorem malcev_preserves {R : G → G → Prop} (hc : Compatible R)
    {x x' y y' z z' : G} (hx : R x x') (hy : R y y') (hz : R z z') :
    R ((@SplitDivisions.malcev G P.magma P.divisions) x y z) ((@SplitDivisions.malcev G P.magma P.divisions) x' y' z') :=
  P.rightDiv_compatible R hc
    (P.mul_compatible R hc hz (P.leftDiv_compatible R hc hy hx))
    (P.leftDiv_compatible R hc hx hx)

theorem compatible_symmetric {R : G → G → Prop} (hc : Compatible R)
    (hr : Reflexive R) : Symmetric R := by
  intro a b hab
  have hh := P.malcev_preserves hc (hr b) hab (hr a)
  simpa only [(@SplitDivisions.malcev_left G P.magma P.divisions), (@SplitDivisions.malcev_right G P.magma P.divisions)] using hh

theorem compatible_transitive {R : G → G → Prop} (hc : Compatible R)
    (hr : Reflexive R) : ∀ ⦃a b c⦄, R a b → R b c → R a c := by
  intro a b c hab hbc
  have hh := P.malcev_preserves hc hab (hr b) hbc
  simpa only [(@SplitDivisions.malcev_left G P.magma P.divisions), (@SplitDivisions.malcev_right G P.magma P.divisions)] using hh

/-- Congruences commute under relational composition, with an explicit witness. -/
theorem congruences_permute (α β : Setoid G) (ha : Compatible α.r) (hb : Compatible β.r)
    {x z : G} (h : ∃ y, α.r x y ∧ β.r y z) : ∃ y, β.r x y ∧ α.r y z := by
  obtain ⟨y, hxy, hyz⟩ := h
  refine ⟨(@SplitDivisions.malcev G P.magma P.divisions) x y z, ?_, ?_⟩
  · have hh := P.malcev_preserves hb (β.refl x) (β.refl y) hyz
    simpa only [(@SplitDivisions.malcev_left G P.magma P.divisions)] using hh
  · have hh := P.malcev_preserves ha hxy (α.refl y) (α.refl z)
    simpa only [(@SplitDivisions.malcev_right G P.magma P.divisions)] using hh

/-- Inclusion of one congruence class already implies inclusion of the congruences. -/
theorem congruence_le_of_class_le (α β : Setoid G) (ha : Compatible α.r)
    (hb : Compatible β.r) (a : G) (hclass : ∀ x, α.r a x → β.r a x) :
    ∀ ⦃x y⦄, α.r x y → β.r x y := by
  intro x y hxy
  let c := (@SplitDivisions.leftDiv G P.magma P.divisions) x a
  have hxc : P.magma.op x c = a := (@SplitDivisions.mul_leftDiv G P.magma P.divisions) x a
  have hα := P.mul_compatible _ ha hxy (α.refl c)
  change α.r (P.magma.op x c) (P.magma.op y c) at hα
  rw [hxc] at hα
  have hβ := P.rightDiv_compatible _ hb (hclass _ hα) (β.refl c)
  rw [← hxc, (@SplitDivisions.rightDiv_mul G P.magma P.divisions), (@SplitDivisions.rightDiv_mul G P.magma P.divisions)] at hβ
  exact hβ

/-- A concrete embedding between any two congruence classes. -/
def classEmbedding (α : Setoid G) (hc : Compatible α.r) (a b : G) :
    {x : G // α.r x a} ↪ {x : G // α.r x b} where
  toFun x := ⟨(@SplitDivisions.transport G P.magma P.divisions) a b x, by
    have hh := P.mul_compatible _ hc x.property (α.refl ((@SplitDivisions.leftDiv G P.magma P.divisions) a b))
    simpa only [(@SplitDivisions.mul_leftDiv G P.magma P.divisions)] using hh⟩
  inj' x y hxy := by
    apply Subtype.ext
    exact (@SplitDivisions.transport_injective G P.magma P.divisions) a b (congrArg Subtype.val hxy)

/-- All congruence classes are equinumerous, even on infinite carriers.
This uses Schröder–Bernstein; it does not assert a term-defined bijection. -/
theorem classes_equinumerous (α : Setoid G) (hc : Compatible α.r) (a b : G) :
    Nonempty ({x : G // α.r x a} ≃ {x : G // α.r x b}) :=
  Function.Embedding.antisymm (P.classEmbedding α hc a b) (P.classEmbedding α hc b a)

end SplitPresentation

/-- Every reflexive compatible relation in any of the five laws is an equivalence. -/
theorem family_compatible_equivalence
    (h : Equation63 G ∨ Equation73 G ∨ Equation118 G ∨ Equation125 G ∨ Equation1692 G)
    (R : G → G → Prop) (hc : Compatible R) (hr : Reflexive R) : Equivalence R := by
  obtain ⟨P⟩ := exists_splitPresentation h
  exact ⟨hr, fun h => P.compatible_symmetric hc hr h, fun h1 h2 => P.compatible_transitive hc hr h1 h2⟩

theorem family_classes_equinumerous
    (h : Equation63 G ∨ Equation73 G ∨ Equation118 G ∨ Equation125 G ∨ Equation1692 G)
    (α : Setoid G) (hc : Compatible α.r) (a b : G) :
    Nonempty ({x : G // α.r x a} ≃ {x : G // α.r x b}) := by
  obtain ⟨P⟩ := exists_splitPresentation h
  exact P.classes_equinumerous α hc a b

/-- E125 supplies the missing inverse of transport directly as a term. -/
theorem transport_retract_125 (h : Equation125 G) (a b x : G) :
    (split73 (equation73_of_125 h)).transport a b
      ((split73 (equation73_of_125 h)).retract a b x) = x :=
  rotate_125 h x _

theorem transport_bijective_125 (h : Equation125 G) (a b : G) :
    Function.Bijective ((split73 (equation73_of_125 h)).transport a b) := by
  let d := split73 (equation73_of_125 h)
  exact ⟨d.transport_injective a b,
    fun x => ⟨d.retract a b x, transport_retract_125 h a b x⟩⟩

spectrum_assert malcev73_left complete
spectrum_assert malcev73_right complete
spectrum_assert malcev118_left complete
spectrum_assert malcev118_right complete
spectrum_assert malcev63_left complete
spectrum_assert malcev63_right complete
spectrum_assert malcev1692_left complete
spectrum_assert malcev1692_right complete
spectrum_assert family_compatible_equivalence complete
spectrum_assert family_classes_equinumerous complete
spectrum_assert SplitPresentation.congruences_permute complete
spectrum_assert SplitPresentation.congruence_le_of_class_le complete
spectrum_assert transport_bijective_125 complete

end E63Family
