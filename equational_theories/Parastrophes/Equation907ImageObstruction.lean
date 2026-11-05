import equational_theories.Parastrophes.ReductionImageObstructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# E907 has no single-equation finite left-division image

The rank-three integer algebra has basis `1,Q,Q²`, with
`Q³ = 2Q - 2` and `P = 1 - Q`. Thus `Q³ = -2P` and
`P² = PQ² - 1`. Its commuting multiplication matrices give
`D(x,y) = Px + Qy`. Over odd characteristic `Q` is invertible and the inverse
operation satisfies E907. Reduction at `P = 1, Q = 0` in characteristic 2
gives left zero, so no identity characterizes the finite division image.
-/
namespace Parastrophes.Eq907ImageObstruction
open Law FreeMagma AffineImage

variable {R : Type*} [CommRing R]

def Q (x : Fin 3 → R) : Fin 3 → R :=
  ![-2 * x 2, x 0 + 2 * x 2, x 1]

def P (x : Fin 3 → R) : Fin 3 → R :=
  ![x 0 + 2 * x 2, x 1 - x 0 - 2 * x 2, x 2 - x 1]

theorem Q_cube (x : Fin 3 → R) : Q (Q (Q x)) = -2 • P x := by
  ext i; fin_cases i <;> simp [P, Q] <;> ring

theorem P_square (x : Fin 3 → R) : P (P x) = P (Q (Q x)) - x := by
  ext i; fin_cases i <;> simp [P, Q] <;> ring

theorem commute (x : Fin 3 → R) : P (Q x) = Q (P x) := by
  ext i; fin_cases i <;> simp [P, Q] <;> ring

@[implicit_reducible] def division : Magma (Fin 3 → R) := ⟨fun x y => P x + Q y⟩

@[simp] theorem division_op (x y : Fin 3 → R) :
    (division (R := R)).op x y = P x + Q y := rfl

/-- `P` is a unit in the integer algebra itself. -/
def Pi (x : Fin 3 → R) : Fin 3 → R := Q (Q x) - P x

/-- Opposite right division; this is the left division of opposite multiplication. -/
@[implicit_reducible] def oppositeRightDivision : Magma (Fin 3 → R) :=
  ⟨fun x y => Pi x - Pi (Q y)⟩

@[simp] theorem oppositeRightDivision_op (x y : Fin 3 → R) :
    (oppositeRightDivision (R := R)).op x y = Pi x - Pi (Q y) := rfl

section Field
variable {K : Type*} [Field K]

/-- `Q⁻¹(y-Px)`, written in coordinates to keep the checks small. -/
@[implicit_reducible] def source : Magma (Fin 3 → K) :=
  ⟨fun x y => ![y 0 + y 1 - x 1, x 1 + y 2 - x 2, x 2 + (x 0 - y 0) / 2]⟩

@[simp] theorem source_op (x y : Fin 3 → K) :
    (source (K := K)).op x y =
      ![y 0 + y 1 - x 1, x 1 + y 2 - x 2, x 2 + (x 0 - y 0) / 2] := rfl

theorem isDivision (h2 : (2 : K) ≠ 0) :
    IsDivision .left (source (K := K)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;> ext i <;> fin_cases i <;>
    simp [P, Q] <;> try field_simp [h2]
  all_goals ring

theorem equation907 (h2 : (2 : K) ≠ 0) : @Equation907 _ (source (K := K)) := by
  intro x y
  simp only [source_op]
  ext i
  fin_cases i <;> simp <;> try field_simp [h2]
  all_goals ring

theorem isDivision_opposite (h2 : (2 : K) ≠ 0) :
    IsDivision .left (opposite (source (K := K))) oppositeRightDivision := by
  change (∀ x y, (source (K := K)).op (oppositeRightDivision.op x y) x = y) ∧
    (∀ x y, oppositeRightDivision.op x ((source (K := K)).op y x) = y)
  constructor <;> intro x y <;> simp only [source_op, oppositeRightDivision_op]
  all_goals
    ext i
    fin_cases i <;> simp [Pi, P, Q] <;> try field_simp [h2]
    all_goals ring

end Field

private def project (x : Fin 3 → Int) : ZMod 2 := (x 0 : ZMod 2)
private def sample (x : ZMod 2) : Fin 3 → Int := ![(x.val : Int), 0, 0]

theorem obstruction {L : NatMagmaLaw}
    (hL : ∀ p : Nat, ∀ hp : p.Prime, 2 < p →
      letI : Fact p.Prime := ⟨hp⟩
      @satisfies _ _ (source (K := ZMod p)) L) : ¬ SingleEquation .fin L .left := by
  refine ReductionImage.obstruction (division (R := Int))
    (fun n => division (R := ZMod n)) ?_ ?_ project sample ?_ ?_
  · intro n x y
    ext i
    fin_cases i <;> simp [reduce, division_op, P, Q]
  · intro p hp hp2
    letI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := ReductionImage.two_ne_zero hp2
    exact ⟨source, hL p hp hp2, isDivision h2⟩
  · intro x
    simp [project, sample]
  · intro x y
    simp [project, division_op, P, Q,
      show (2 : ZMod 2) = 0 by decide]

theorem right_obstruction {L : NatMagmaLaw}
    (hL : ∀ p : Nat, ∀ hp : p.Prime, 2 < p →
      letI : Fact p.Prime := ⟨hp⟩
      @satisfies _ _ (source (K := ZMod p)) L) : ¬ SingleEquation .fin L .right := by
  have hn : ¬ SingleEquation .fin L.dual .left := by
    refine ReductionImage.obstruction (oppositeRightDivision (R := Int))
      (fun n => oppositeRightDivision (R := ZMod n)) ?_ ?_ project sample ?_ ?_
    · intro n x y
      ext i
      fin_cases i <;> simp [reduce, oppositeRightDivision_op, Pi, P, Q]
    · intro p hp hp2
      letI : Fact p.Prime := ⟨hp⟩
      exact ⟨opposite source, (satisfies_opposite source L).mpr (hL p hp hp2),
        isDivision_opposite (ReductionImage.two_ne_zero hp2)⟩
    · intro x
      simp [project, sample]
    · intro x y
      simp [project, oppositeRightDivision_op, Pi, P, Q,
        show (2 : ZMod 2) = 0 by decide]
  exact fun h => hn (singleEquation_dual h)

/-- There is no uniform reverse term, even on this particular family of finite
left-division images. -/
theorem no_uniform_finite_inverse :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ p : Nat, p.Prime → 2 < p →
      IsDivision .left (division (R := ZMod p)) (termMagma division t) := by
  refine ReductionImage.no_uniform_inverse (division (R := Int))
    (fun n => division (R := ZMod n)) ?_ project sample ?_ ?_
  · intro n x y
    ext i
    fin_cases i <;> simp [reduce, division_op, P, Q]
  · intro x
    simp [project, sample]
  · intro x y
    simp [project, division_op, P, Q,
      show (2 : ZMod 2) = 0 by decide]

/-- The analogous obstruction for the opposite right-division family. -/
theorem no_uniform_finite_opposite_right_inverse :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ p : Nat, p.Prime → 2 < p →
      IsDivision .left (oppositeRightDivision (R := ZMod p))
        (termMagma oppositeRightDivision t) := by
  refine ReductionImage.no_uniform_inverse (oppositeRightDivision (R := Int))
    (fun n => oppositeRightDivision (R := ZMod n)) ?_ project sample ?_ ?_
  · intro n x y
    ext i
    fin_cases i <;> simp [reduce, oppositeRightDivision_op, Pi, P, Q]
  · intro x
    simp [project, sample]
  · intro x y
    simp [project, oppositeRightDivision_op, Pi, P, Q,
      show (2 : ZMod 2) = 0 by decide]

end Parastrophes.Eq907ImageObstruction

namespace Parastrophes.Catalogue

/-- An integral rank-three family specializes to left zero at 2. This settles
the finite left-image characterization question without deciding whether
every finite E907 model has right division. -/
@[parastrophe_result] theorem left_noSingleEquation907_fin :
    ¬ SingleEquation .fin Law907 .left := by
  apply Eq907ImageObstruction.obstruction
  intro p hp hp2
  letI : Fact p.Prime := ⟨hp⟩
  apply (@Law907.models_iff _ (Eq907ImageObstruction.source (K := ZMod p))).mpr
  apply Eq907ImageObstruction.equation907
  exact ReductionImage.two_ne_zero hp2

/-- The same family also obstructs the actual right-division image, independently
of the open question whether all finite E907 models possess right division. -/
@[parastrophe_result] theorem right_noSingleEquation907_fin :
    ¬ SingleEquation .fin Law907 .right := by
  apply Eq907ImageObstruction.right_obstruction
  intro p hp hp2
  letI : Fact p.Prime := ⟨hp⟩
  apply (@Law907.models_iff _ (Eq907ImageObstruction.source (K := ZMod p))).mpr
  exact Eq907ImageObstruction.equation907 (ReductionImage.two_ne_zero hp2)

end Parastrophes.Catalogue
