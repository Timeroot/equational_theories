import equational_theories.Equations.All
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.EquivFin

/-! Translation constraints for finite E467 models.

Write `D x = x*x`, `T x = x*(x*x)`, and `L x y = x*y`. Squaring and
`T` are inverse permutations. The unique fixed point of both `L x` and
`(L x)²` is `D² x`. Thus a left translation has precisely one fixed point
and no two-cycles; its cycle through `x` has length one or four.

These are algebraic reductions, independent of any finite-model search. -/

namespace Spectrum.E467

variable {G : Type*} [Finite G] (p : G → G → G)
  (h : ∀ x y, x = p y (p x (p x (p y y))))

include h

theorem left_injective (x : G) : Function.Injective (p x) :=
  Finite.injective_iff_surjective.mpr fun y =>
    ⟨p y (p y (p x x)), (h y x).symm⟩

def square (x : G) : G := p x x
def root (x : G) : G := p x (square p x)

theorem root_square (x : G) : root p (square p x) = x := by
  apply left_injective p h x
  exact (h (p x x) x).symm

theorem square_injective : Function.Injective (square p) :=
  Function.LeftInverse.injective (root_square p h)

theorem square_root (x : G) : square p (root p x) = x := by
  obtain ⟨y, rfl⟩ := Finite.surjective_of_injective (square_injective p h) x
  rw [root_square p h]

/-- The law recovers the square of the left factor from a product and its
right factor. Two left cancellations and one square cancellation suffice. -/
theorem right_injective (y : G) : Function.Injective (fun x => p x y) := by
  intro a b hab
  change p a y = p b y at hab
  have recover (a : G) : p (p a y) (p (p a y) (square p a)) = y := by
    apply left_injective p h a
    exact (h (p a y) a).symm
  have hh := (recover a).trans (recover b).symm
  rw [hab] at hh
  exact square_injective p h (left_injective p h _ (left_injective p h _ hh))

/-- A square of a left translation has exactly one fixed point. -/
theorem square_translation_fixed_iff (x y : G) :
    p x (p x y) = y ↔ y = square p (square p x) := by
  constructor
  · intro hy
    have hx : x = root p (root p y) := by
      have hh := h x (root p y)
      change x = p (root p y) (p x (p x (square p (root p y)))) at hh
      rw [square_root p h, hy] at hh
      change x = p (root p y) (square p (root p y))
      rw [square_root p h]
      exact hh
    calc
      y = square p (square p (root p (root p y))) := by
        rw [square_root p h, square_root p h]
      _ = square p (square p x) := congrArg (fun z => square p (square p z)) hx.symm
  · rintro rfl
    apply left_injective p h (square p x)
    exact (h x (square p x)).symm.trans (root_square p h x).symm

theorem translation_fixed_iff (x y : G) :
    p x y = y ↔ y = square p (square p x) := by
  constructor
  · intro hy
    apply (square_translation_fixed_iff p h x y).mp
    rw [hy, hy]
  · intro hy
    have hq := (square_translation_fixed_iff p h x y).mpr hy
    have hqq : p x (p x (p x y)) = p x y := congrArg (p x) hq
    exact ((square_translation_fixed_iff p h x (p x y)).mp hqq).trans hy.symm

theorem no_two_cycle (x y z : G) (hy : p x y = z) (hz : p x z = y) : y = z := by
  have hq : p x (p x y) = y := by rw [hy, hz]
  have hf := (translation_fixed_iff p h x y).mpr
    ((square_translation_fixed_iff p h x y).mp hq)
  exact hf.symm.trans hy

theorem square_period_two (x : G) (hx : square p (square p x) = x) :
    square p x = x :=
  (translation_fixed_iff p h x x).mpr hx.symm

/-- Squaring has no nontrivial three-cycles either. -/
theorem square_period_three (x : G)
    (hx : square p (square p (square p x)) = x) : square p x = x := by
  have ht : root p x = square p (square p x) :=
    square_injective p h ((square_root p h x).trans hx.symm)
  have hq := (square_translation_fixed_iff p h x (square p (square p x))).mpr rfl
  have he : x = square p (square p x) :=
    left_injective p h x (left_injective p h x (ht.trans hq.symm))
  exact square_period_two p h x he.symm

omit [Finite G] in
theorem self_four_cycle (x : G) : p x (p x (p x (p x x))) = x :=
  (h x x).symm

end Spectrum.E467
