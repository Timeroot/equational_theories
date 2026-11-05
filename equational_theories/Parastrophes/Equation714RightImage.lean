import equational_theories.Parastrophes.DivisionTerms

/-!
# Two constraints on E714's right-division image

If R is right division of M, then `R(x,y)=y*(y*(y*x))` in M notation.
On the diagonal the y-row has period dividing four. Consequently three
successive right multiplications by x in R recover M's square at x.
This is a square-recovery formula, not a recovery of general multiplication.

E714 is also flexible. Translating flexibility into R gives the second
identity below, without a finiteness assumption. Neither necessary condition
is registered as a characterization of the image.
-/
namespace Parastrophes.Eq714RightImage
open Law

variable {G : Type} (M : Magma G) (h : @Equation714 G M)
include h

private theorem right_division : IsDivision .right M
    ⟨fun x y => M.op y (M.op y (M.op y x))⟩ :=
  Catalogue.right_term714 G M trivial ((@Law714.models_iff G M).mpr h)

theorem square_recovery (R : Magma G) (hd : IsDivision .right M R) (x : G) :
    R.op (R.op (R.op x x) x) x = M.op x x := by
  have hr := right_division M h
  have formula (u v : G) : R.op u v = M.op v (M.op v (M.op v u)) :=
    congrArg (fun D : Magma G => D.op u v) (division_unique hd hr)
  have fourth : M.op x (M.op x (M.op x (M.op x x))) = x := hr.2 x x
  simp only [formula]
  rw [fourth, fourth]

theorem flexible (x y : G) : M.op (M.op x y) x = M.op x (M.op y x) := by
  have hl := Catalogue.left_term714 G M trivial ((@Law714.models_iff G M).mpr h)
  have hi := (sideQuasigroup_of_division hl x).1
  have he := (h y x).symm.trans ((right_division M h).2 y x).symm
  exact hi (hi he)

/-- A left absorption is symmetric. This uses flexibility and cancellation,
not finiteness. -/
theorem absorption_symmetric (x y : G) (he : M.op x y = x) : M.op y x = x := by
  have hl := Catalogue.left_term714 G M trivial ((@Law714.models_iff G M).mpr h)
  apply (sideQuasigroup_of_division hl x).1
  exact (flexible M h x y).symm.trans (by rw [he])

/-- Cubing a row introduces no new fixed points. This excludes three-cycles
of a row; it does not exclude longer cycles whose lengths are divisible by 3. -/
theorem row_cube_fixed_iff (x y : G) :
    M.op x (M.op x (M.op x y)) = y ↔ M.op x y = y := by
  constructor
  · intro he
    have hr := (right_division M h).1 y x
    change M.op (M.op x (M.op x (M.op x y))) x = y at hr
    rw [he] at hr
    exact absorption_symmetric M h y x hr
  · intro he
    rw [he, he, he]

/-- A pure identity obtained by eliminating multiplication from flexibility. -/
theorem divided_flexible (R : Magma G) (hd : IsDivision .right M R) (x y : G) :
    R.op (R.op x (R.op x y)) (R.op y (R.op x y)) = R.op x y := by
  let a := R.op x y
  let b := R.op y a
  have he := flexible M h a b
  have hab : M.op b a = y := hd.1 y a
  have hay : M.op a y = x := hd.1 x y
  rw [hab, hay] at he
  have hr : R.op x a = M.op a b := by rw [← he, hd.2]
  change R.op (R.op x a) b = a
  rw [hr, hd.2]

end Parastrophes.Eq714RightImage

namespace Parastrophes.Eq714RightImage.SquareCounterexample

/-- Flexibility does not make source squaring an endomorphism. This small
example is also saved in the research sample pool to prevent that assumption
from slipping into subsequent term searches. -/
@[implicit_reducible] def source : Magma (Fin 6) := ⟨![
  ![0,1,4,5,2,3], ![1,2,3,0,5,4], ![4,3,2,1,0,5],
  ![5,0,1,3,4,2], ![2,5,0,4,3,1], ![3,4,5,2,1,0]]⟩

theorem source_law : @Equation714 (Fin 6) source := by decide

theorem square_not_endomorphism :
    source.op (source.op 0 1) (source.op 0 1) ≠
      source.op (source.op 0 0) (source.op 1 1) := by decide

end Parastrophes.Eq714RightImage.SquareCounterexample
