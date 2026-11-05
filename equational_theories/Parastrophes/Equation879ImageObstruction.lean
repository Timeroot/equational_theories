import equational_theories.Parastrophes.OptionReductionImage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# E879's finite left-division image is not equational

On two Gaussian coordinates put `M(x,y) = -x + i*y`, with left division
`D(x,y) = -i*(x+y)`. Write `S = i-1` for the square map. Adjoin a right zero
whose division row is `H(u,v) = (S*v,u)`. Since `H² = S`, its inverse `F`
satisfies `F²(S*x) = x`, exactly the extra condition for E879.

This is an actual finite division image at every odd prime. Its integral
formulas also reduce modulo 2, where `S` and hence `H` have a kernel. The bad
17-element reduction satisfies every identity common to the genuine images,
but cannot itself be a left-division image.
-/
namespace Parastrophes.Eq879ImageObstruction
open Law FreeMagma OptionReductionImage

variable {R : Type} [CommRing R]

def oldOp (x y : Fin 4 → R) : Fin 4 → R :=
  ![-x 0 - y 1, -x 1 + y 0, -x 2 - y 3, -x 3 + y 2]
def oldDiv (x y : Fin 4 → R) : Fin 4 → R :=
  ![x 1 + y 1, -x 0 - y 0, x 3 + y 3, -x 2 - y 2]
def H (x : Fin 4 → R) : Fin 4 → R := ![-x 2 - x 3, x 2 - x 3, x 0, x 1]

@[implicit_reducible] def division : Magma (Carrier 4 R) :=
  FoldedExtensions.extension oldDiv H

section Field
variable {K : Type} [Field K]

def F (x : Fin 4 → K) : Fin 4 → K :=
  ![x 2, x 3, (x 1 - x 0) / 2, -(x 0 + x 1) / 2]

@[implicit_reducible] def source : Magma (Carrier 4 K) :=
  FoldedExtensions.extension oldOp F

theorem isDivision (h2 : (2 : K) ≠ 0) :
    IsDivision .left (source (K := K)) division := by
  apply extension_division
  · constructor <;> intro x y <;> ext i <;> fin_cases i <;> simp [oldOp, oldDiv]
  · intro x; ext i; fin_cases i <;> simp [F, H] <;> try field_simp [h2]
    all_goals ring
  · intro x; ext i; fin_cases i <;> simp [F, H] <;> try field_simp [h2]
    all_goals ring

theorem equation879 (h2 : (2 : K) ≠ 0) : @Equation879 _ (source (K := K)) := by
  rintro (_ | x) (_ | y)
  · rfl
  · rfl
  · change some x = some (F (F (oldOp x x)))
    congr 1
    ext i; fin_cases i <;> simp [F, oldOp] <;> try field_simp [h2]
    all_goals ring
  · change some x = some (oldOp y (oldOp (oldOp x y) (oldOp x x)))
    congr 1
    ext i; fin_cases i <;> simp [oldOp]

end Field

theorem reduce_op (n : Nat) (x y : Carrier 4 Int) :
    reduce n ((division (R := Int)).op x y) =
      (division (R := ZMod n)).op (reduce n x) (reduce n y) := by
  cases x <;> cases y
  all_goals first
    | rfl
    | apply congrArg some; funext i; fin_cases i <;> simp [AffineImage.reduce, oldDiv, H]

theorem bad_reduction : ¬ IsSideQuasigroup .left (division (R := ZMod 2)) := by
  intro h
  have he := (h none).1 (a₁ := some ![0, 0, 0, 0]) (a₂ := some ![0, 0, 1, 1])
    (by decide)
  have hh := congrFun (Option.some.inj he) 2
  exact (by decide : (0 : ZMod 2) ≠ 1) hh

/-- This transfer statement also rules out arbitrary equational axiom sets. -/
theorem common_identity {L : NatMagmaLaw}
    (h : ∀ p : Nat, p.Prime → 2 < p → @satisfies _ _ (division (R := ZMod p)) L) :
    @satisfies _ _ (division (R := ZMod 2)) L :=
  two_of_prime_reductions division (fun n => division (R := ZMod n)) reduce_op h

/-- No uniform term recovers the original multiplication from these divisions. -/
theorem no_uniform_finite_inverse :
    ¬ ∃ t : FreeMagma (Fin 2), ∀ p : Nat, p.Prime → 2 < p →
      IsDivision .left (division (R := ZMod p)) (termMagma division t) :=
  OptionReductionImage.no_uniform_inverse division (fun n => division (R := ZMod n))
    reduce_op bad_reduction

end Parastrophes.Eq879ImageObstruction

namespace Parastrophes.Catalogue

/-- A right-zero extension of Gaussian division models degenerates at 2,
ruling out every defining identity for the finite left-division image. -/
@[parastrophe_result] theorem left_noSingleEquation879_fin :
    ¬ SingleEquation .fin Law879 .left := by
  apply OptionReductionImage.obstruction Eq879ImageObstruction.division
    (fun n => Eq879ImageObstruction.division (R := ZMod n)) Eq879ImageObstruction.reduce_op
  · intro p hp hp2
    letI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := ReductionImage.two_ne_zero hp2
    exact ⟨Eq879ImageObstruction.source,
      (@Law879.models_iff _ (Eq879ImageObstruction.source (K := ZMod p))).mpr (Eq879ImageObstruction.equation879 h2),
      Eq879ImageObstruction.isDivision h2⟩
  · exact Eq879ImageObstruction.bad_reduction

end Parastrophes.Catalogue
