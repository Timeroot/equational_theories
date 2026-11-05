import equational_theories.Parastrophes.Equation1516Image
import Mathlib.Algebra.Group.Hom.Defs

/-!
# The E1516 image candidate is exact for finite affine magmas

Let `x * y = a(x) + b(y) + k` on a finite abelian group, where `a` and `b`
are additive endomorphisms. They need not commute or be invertible initially.
The eight-operation identity `Short` forces both maps to be invertible.
Consequently it characterizes E1516's left-division image within this entire
class, including arbitrary constant offsets.
The coefficient maps are also proved to commute, as a consequence rather
than a hypothesis.

The key observation uses only the instance with the two parameters zero.
After expanding that instance, all dependence on x passes through b(a(x)).
More precisely its variable part is `a(b(t)) + b(b(b(t))) + t`, with
`t=b(a(x))`; the remaining summand is independent of x.
Thus b ∘ a is injective. Finiteness makes a surjective, and then b injective
and surjective. The existing cancellation-based converse now applies.

This is a restricted characterization, not a new answer to `SingleEquation`:
the four-element non-affine counterexample in `Equation1516Image` still
refutes the identity among arbitrary magmas. No catalogue attribute is added.
-/
namespace Parastrophes.Eq1516AffineImage
open Law

variable {G : Type} [AddCommGroup G]

@[implicit_reducible] def affine (a b : G →+ G) (k : G) : Magma G :=
  ⟨fun x y => a x + b y + k⟩

/-- Expanding one instance of the candidate exposes a compositional left
inverse of b ∘ a. This part does not use finiteness. -/
theorem injective_comp (a b : G →+ G) (k : G)
    (h : Eq1516Image.Short (affine a b k)) : Function.Injective (b ∘ a) := by
  intro x y he
  change b (a x) = b (a y) at he
  have hx := h x 0 0
  have hy := h y 0 0
  have hh : (affine a b k).op (Eq1516Image.cross (affine a b k) x 0)
      ((affine a b k).op x (Eq1516Image.cross (affine a b k) x 0)) =
      (affine a b k).op (Eq1516Image.cross (affine a b k) y 0)
      ((affine a b k).op y (Eq1516Image.cross (affine a b k) y 0)) := by
    dsimp only [Eq1516Image.cross, Magma.op, affine]
    simp only [map_add, map_zero, add_zero, zero_add]
    rw [he]
  exact hx.symm.trans (hh.trans hy)

/-- No invertibility or commutation of the coefficient maps is assumed. -/
theorem coefficients_bijective [Finite G] (a b : G →+ G) (k : G)
    (h : Eq1516Image.Short (affine a b k)) :
    Function.Bijective a ∧ Function.Bijective b := by
  have hab := injective_comp a b k h
  have ha : Function.Injective a := fun _ _ he => hab (congrArg b he)
  have has := Finite.surjective_of_injective ha
  have hb : Function.Injective b := by
    intro x y he
    obtain ⟨u, rfl⟩ := has x
    obtain ⟨v, rfl⟩ := has y
    exact congrArg a (hab he)
  exact ⟨⟨ha, has⟩, ⟨hb, Finite.surjective_of_injective hb⟩⟩

private theorem affine_rows (a b : G →+ G) (k : G)
    (hb : Function.Bijective b) : IsSideQuasigroup .left (affine a b k) := by
  intro x
  constructor
  · intro y z he
    apply hb.1
    exact add_left_cancel (add_right_cancel he)
  · intro y
    obtain ⟨z, hz⟩ := hb.2 (y - k - a x)
    refine ⟨z, ?_⟩
    change a x + b z + k = y
    rw [hz]
    abel

/-- The identity also forces the initially arbitrary coefficient maps to
commute. Thus noncommuting matrix coefficients cannot evade the criterion. -/
theorem coefficients_commute [Finite G] (a b : G →+ G) (k : G)
    (h : Eq1516Image.Short (affine a b k)) : Function.Commute a b := by
  obtain ⟨ha, hb⟩ := coefficients_bijective a b k h
  have hc := (Eq1516Image.criterion_of_short (affine a b k)
    (affine_rows a b k hb) h).1
  have relation (x : G) : a x + b (a x) + b (b (b x)) = 0 := by
    calc
      _ = Eq1516Image.cross (affine a b k) 0 x -
          Eq1516Image.cross (affine a b k) 0 0 := by
        dsimp only [Eq1516Image.cross, Magma.op, affine]
        simp only [map_add, map_zero, add_zero, zero_add]
        abel
      _ = 0 := by rw [hc, hc, sub_self]
  let e : G →+ G := AddMonoidHom.id G + b
  have ea (x : G) : e (a x) = -b (b (b x)) :=
    eq_neg_iff_add_eq_zero.mpr (relation x)
  have ei : Function.Injective e := by
    intro x y he
    obtain ⟨u, rfl⟩ := ha.2 x
    obtain ⟨v, rfl⟩ := ha.2 y
    rw [ea, ea] at he
    exact congrArg a (hb.1 (hb.1 (hb.1 (neg_injective he))))
  intro x
  apply ei
  calc
    e (a (b x)) = -b (b (b (b x))) := ea (b x)
    _ = b (e (a x)) := by rw [ea, map_neg]
    _ = e (b (a x)) := by change b (a x + b (a x)) = b (a x) + b (b (a x)); rw [map_add]

/-- An exact finite affine characterization. The unrestricted single-law
question is separate and is not asserted by this theorem. -/
theorem characterizes_fin [Finite G] (a b : G →+ G) (k : G) :
    Eq1516Image.Short (affine a b k) ↔ InImage Law1516 .left (affine a b k) := by
  constructor
  · intro h
    have hb := (coefficients_bijective a b k h).2
    exact (Eq1516Image.characterizes_leftQuasigroups_fin (affine a b k)
      (affine_rows a b k hb)).mp h
  · exact Eq1516Image.short_of_image (affine a b k)

end Parastrophes.Eq1516AffineImage
