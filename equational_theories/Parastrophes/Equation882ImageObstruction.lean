import equational_theories.Parastrophes.ReductionImageObstructions
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# E882 has no single-equation finite left-division image

Use the rank-two integer algebra with `Q² = -2` and `P = Q - 1`.
Then `P² = -1 - 2Q` and `PQ = QP`. The operation `D(x,y) = Px + Qy` is genuine left division
of an E882 model over every field of odd characteristic. At characteristic 2,
evaluation at `P = 1, Q = 0` instead gives the two-element left-zero magma.
-/
namespace Parastrophes.Eq882ImageObstruction
open Law FreeMagma AffineImage

variable {R : Type*} [CommRing R]

def Q (x : Fin 2 → R) : Fin 2 → R := ![-2 * x 1, x 0]
def P (x : Fin 2 → R) : Fin 2 → R := ![-x 0 - 2 * x 1, x 0 - x 1]

theorem Q_square (x : Fin 2 → R) : Q (Q x) = -2 • x := by
  ext i; fin_cases i <;> simp [Q]

theorem P_square (x : Fin 2 → R) : P (P x) = -x - 2 • Q x := by
  ext i; fin_cases i <;> simp [P, Q] <;> ring

theorem commute (x : Fin 2 → R) : P (Q x) = Q (P x) := by
  ext i; fin_cases i <;> simp [P, Q] <;> ring

@[implicit_reducible] def division : Magma (Fin 2 → R) := ⟨fun x y => P x + Q y⟩

@[simp] theorem division_op (x y : Fin 2 → R) :
    (division (R := R)).op x y = P x + Q y := rfl

section Field
variable {K : Type*} [Field K]

@[implicit_reducible] def source : Magma (Fin 2 → K) :=
  ⟨fun x y i => ((Q (P x)) i - (Q y) i) / 2⟩

@[simp] theorem source_op (x y : Fin 2 → K) :
    (source (K := K)).op x y = (fun i => ((Q (P x)) i - (Q y) i) / 2) := rfl

theorem isDivision (h2 : (2 : K) ≠ 0) :
    IsDivision .left (source (K := K)) division := by
  constructor <;> intro x y <;> simp only [source_op, division_op] <;> ext i <;> fin_cases i <;>
    simp [P, Q] <;> try field_simp [h2]
  all_goals ring

theorem equation882 (h2 : (2 : K) ≠ 0) : @Equation882 _ (source (K := K)) := by
  intro x y
  simp only [source_op]
  ext i
  fin_cases i <;> simp [P, Q] <;> try field_simp [h2]
  all_goals ring

end Field

private def project (x : Fin 2 → Int) : ZMod 2 := (x 0 : ZMod 2)
private def sample (x : ZMod 2) : Fin 2 → Int := ![(x.val : Int), 0]

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

/-- Although each finite model permits a reverse division term, no one term
works on all the odd-prime reductions of this family. -/
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

end Parastrophes.Eq882ImageObstruction

namespace Parastrophes.Catalogue

/-- An integral rank-two family specializes to left zero at 2, ruling out
every defining identity for E882's finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation882_fin :
    ¬ SingleEquation .fin Law882 .left := by
  apply Eq882ImageObstruction.obstruction
  intro p hp hp2
  letI : Fact p.Prime := ⟨hp⟩
  apply (@Law882.models_iff _ (Eq882ImageObstruction.source (K := ZMod p))).mpr
  apply Eq882ImageObstruction.equation882
  exact ReductionImage.two_ne_zero hp2

end Parastrophes.Catalogue
