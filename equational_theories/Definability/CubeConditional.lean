import equational_theories.Definability.CaseSplit
import equational_theories.Definability.FiniteFlavour
import equational_theories.Definability.CubeTwists
import equational_theories.ManuallyProved.Equation3342

/-!
# A conditional interpretation of E3545 in finite E3342 magmas

Write `q x = x*x` and `s x = x*(x*x)`. The operation
`g(x,y) = if q x = q y then x*y else s(x*y)` has the same diagonal as
the source, and its right cube is the source's left cube. Thus the source's
twisted commutativity becomes exactly E3545 for `g`.

The right-cube calculation uses the finite E3342 consequences E3522 and E4118.
No claim of recoverability or of an infinite-carrier interpretation is made.
-/

open FreeMagma Law Law.MagmaLaw

namespace CubeConditional

private abbrev x : FreeMagma (Fin 2) := .Leaf 0
private abbrev y : FreeMagma (Fin 2) := .Leaf 1
private abbrev p : FreeMagma (Fin 2) := x ⋆ y

/-- Equality of the two squares selects the unchanged product. -/
def forward : QFOp :=
  .ite (x ⋆ x) (y ⋆ y) (.leaf p) (.leaf (p ⋆ (p ⋆ p)))

variable {G : Type} (M : Magma G)

abbrev square (a : G) := M.op a a
abbrev leftCube (a : G) := M.op a (square M a)
abbrev rightCube (a : G) := M.op (square M a) a

open scoped Classical in
theorem forward_apply (a b : G) :
    (forward.magma M).op a b =
      if square M a = square M b then M.op a b else leftCube M (M.op a b) := rfl

theorem forward_square (a : G) :
    (forward.magma M).op a a = square M a := by
  classical
  rw [forward_apply, if_pos rfl]

variable (h : @Equation3342 G M)
include h

theorem square_leftCube (a : G) : square M (leftCube M a) = square M a :=
  CubeTwists.square_twist M.op (leftCube M) h a

/-- An idempotent square has equal left and right cubes; finiteness is not needed. -/
theorem cubes_eq_of_square_idempotent (a : G)
    (ha : square M (square M a) = square M a) :
    rightCube M a = leftCube M a := by
  have hs : leftCube M (square M a) = square M a := by
    change M.op (square M a) (square M (square M a)) = square M a
    rw [ha]
    exact ha
  exact (h (square M a) a).trans (congrArg (M.op a) hs)

section finite
variable [Finite G]

theorem absorb_rightCube_left (a b : G) :
    M.op (rightCube M a) b = M.op a b :=
  (@Eq3342.Finite.Equation3342_implies_Equation4118 G M _ h a b).symm

theorem absorb_rightCube_right (a b : G) :
    M.op a (rightCube M b) = M.op a b :=
  (@Eq3342.Finite.Equation3342_implies_Equation3522 G M _ h a b).symm

theorem square_rightCube (a : G) : square M (rightCube M a) = square M a := by
  change M.op (rightCube M a) (rightCube M a) = M.op a a
  rw [absorb_rightCube_left M h, absorb_rightCube_right M h]

theorem leftCube_rightCube (a : G) : leftCube M (rightCube M a) = leftCube M a := by
  change M.op (rightCube M a) (square M (rightCube M a)) = M.op a (square M a)
  rw [square_rightCube M h, absorb_rightCube_left M h]

/-- The new right cube is exactly the original left cube. -/
theorem forward_rightCube (a : G) :
    (forward.magma M).op ((forward.magma M).op a a) a = leftCube M a := by
  classical
  rw [forward_square, forward_apply]
  split_ifs with ha
  · exact cubes_eq_of_square_idempotent M h a ha
  · exact leftCube_rightCube M h a

theorem target : @Equation3545 G (forward.magma M) := by
  classical
  intro a b
  rw [forward_rightCube M h, forward_apply, forward_apply, square_leftCube M h]
  rw [h a b]
  by_cases hab : square M a = square M b
  · rw [if_pos hab, if_pos hab.symm]
  · rw [if_neg hab, if_neg (Ne.symm hab)]

end finite

omit h M in
/-- The same recipe fails on the existing infinite E3342 example. This rejects
only this recipe, not the unrestricted definability arrow. -/
theorem infinite_recipe_failure :
    ¬ @Equation3545 (Option (ℕ × ℕ)) (forward.magma ⟨Eq3342.op⟩) := by
  intro hf
  have he := hf (some (0, 0)) (some (0, 0))
  norm_num [forward_apply, square, leftCube, Eq3342.op] at he
  cases he

end CubeConditional

/-- A quantifier-free interpretation, valid on all finite E3342 magmas. -/
theorem Law.MagmaLaw.Equation3545_definableFromFin_Equation3342_conditional :
    Law3545.DefinableFromFin Law3342 := by
  intro G _ M hM
  refine ⟨CubeConditional.forward.magma M, ?_, CubeConditional.forward.definable_graph M⟩
  exact (@Law3545.models_iff G (CubeConditional.forward.magma M)).mpr
    (CubeConditional.target M ((@Law3342.models_iff G M).mp hM))

/-- info: 'Law.MagmaLaw.Equation3545_definableFromFin_Equation3342_conditional' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Law.MagmaLaw.Equation3545_definableFromFin_Equation3342_conditional
