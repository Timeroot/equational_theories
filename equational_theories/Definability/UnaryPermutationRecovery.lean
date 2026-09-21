import equational_theories.Definability.Invariant

/-! In an E1202 magma every one-variable term induces a permutation.
This obstructs recovery of an operation whose square map is not bijective. -/

open FirstOrder Law Law.MagmaLaw
namespace UnaryPermutationRecovery

variable {G : Type} (M : Magma G) (h : @Equation1202 G M)
local infixl:70 " * " => M.op

include h in
theorem invol (x y : G) : x * (x * y) = y := by
  have h1096 : ∀ a b c : G, b * ((a * (c * b)) * a) = a :=
    fun a b c => (h a b a c).symm
  have h1 := h1096 y x (x * (x * y))
  have h2 := h1096 x y x
  grind

include h in
theorem row_two (a b x y : G) : (a * (b * x)) * y = x * y := by
  have e := congrArg (fun t => x * t) (h y x a b)
  simpa only [invol M h] using e.symm

def square (x : G) : G := x * x
def unsquare (x : G) : G := (x * x) * x

include h in
theorem row_square_square (x y : G) : square M (square M x) * y = x * y :=
  row_two M h (square M x) x x y

include h in
theorem row_product (a b y : G) : (a * b) * y = square M b * y := by
  have e := row_two M h a b (square M b) y
  simpa only [square, invol M h] using e

include h in
theorem square_unsquare (x : G) : square M (unsquare M x) = x := by
  have e : unsquare M x * unsquare M x = square M x * unsquare M x :=
    row_product M h (square M x) x (unsquare M x)
  exact e.trans (invol M h (square M x) x)

include h in
theorem unsquare_square (x : G) : unsquare M (square M x) = x := by
  have e := row_square_square M h x (square M x)
  exact e.trans (invol M h x x)

include h in
theorem square_bijective : Function.Bijective (square M) :=
  ⟨Function.LeftInverse.injective (unsquare_square M h),
    Function.RightInverse.surjective (square_unsquare M h)⟩

include h in
theorem unsquare_bijective : Function.Bijective (unsquare M) :=
  ⟨Function.LeftInverse.injective (square_unsquare M h),
    Function.RightInverse.surjective (unsquare_square M h)⟩

def RowPair (flip : Bool) (f : G → G) : Prop :=
  if flip then
    (∀ x y, f x * y = square M x * y) ∧
    (∀ x y, square M (f x) * y = x * y)
  else
    (∀ x y, f x * y = x * y) ∧
    (∀ x y, square M (f x) * y = square M x * y)

def Good (f : G → G → G) : Prop :=
  Function.Bijective (fun x => f x x) ∧ ∃ flip, RowPair M flip (fun x => f x x)

include h in
theorem good_invariant : M.IsCloneInvariant (Good M) where
  fst := ⟨Function.bijective_id, false, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  snd := ⟨Function.bijective_id, false, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  comp := by
    rintro f g ⟨hf, a, ha⟩ ⟨hg, b, hb⟩
    have hrow : RowPair M (!b) (fun x => f x x * g x x) := by
      cases b <;> simp only [RowPair, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte] at hb ⊢
      · exact ⟨fun x y => (row_product M h _ _ _).trans (hb.2 x y),
          fun x y => (row_two M h _ _ _ _).trans (hb.1 x y)⟩
      · exact ⟨fun x y => (row_product M h _ _ _).trans (hb.2 x y),
          fun x y => (row_two M h _ _ _ _).trans (hb.1 x y)⟩
    refine ⟨?_, !b, hrow⟩
    cases a <;> cases b <;> simp only [RowPair, Bool.false_eq_true, ↓reduceIte] at ha hb
    · have e : (fun x => f x x * g x x) = fun x => square M (g x x) := by
        funext x
        exact (ha.1 x _).trans (hb.1 x _).symm
      rw [e]
      exact (square_bijective M h).comp hg
    · have e : (fun x => f x x * g x x) = fun x => unsquare M (g x x) := by
        funext x
        exact (ha.1 x _).trans (hb.2 x _).symm
      rw [e]
      exact (unsquare_bijective M h).comp hg
    · have e : (fun x => f x x * g x x) = fun x => unsquare M (g x x) := by
        funext x
        exact (ha.1 x _).trans (hb.2 x _).symm
      rw [e]
      exact (unsquare_bijective M h).comp hg
    · have e : (fun x => f x x * g x x) = fun x => square M (g x x) := by
        funext x
        exact (ha.1 x _).trans (hb.1 x _).symm
      rw [e]
      exact (square_bijective M h).comp hg

theorem not_termStructuralOnMagma (N : Magma G)
    (hbad : ¬ Function.Bijective (fun x => N.op x x)) :
    ¬ Law1202.TermStructuralOnMagma N := by
  rintro ⟨M, hM, _, hback⟩
  exact hbad ((good_invariant M ((@Law1202.models_iff G M).mp hM)).of_termDefinable hback).1

end UnaryPermutationRecovery
