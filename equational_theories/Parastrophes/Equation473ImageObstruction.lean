import equational_theories.Parastrophes.OptionReductionImage
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# E473's finite left-division image is not equational

On Gaussian coordinates use `M(x,y) = 3i*x - i*y`, with division
`D(x,y) = 3*x + i*y`. Its square map is `S(x)=2i*x`. Adjoin a right zero
whose division row is also `S`, with inverse `F(x)=-i*x/2`. The extra E473
condition is `F(M(x,F(M(x,x))))=x`, which follows twice from `F(S(x))=x`.
At characteristic two, the new division row is zero. The five-element
reduction is not a left-division image, although it satisfies every common
identity of the finite images in the odd-prime family.
-/
namespace Parastrophes.Eq473ImageObstruction
open Law FreeMagma OptionReductionImage

variable {R : Type} [CommRing R]

def oldOp (x y : Fin 2 → R) : Fin 2 → R :=
  ![-3 * x 1 + y 1, 3 * x 0 - y 0]
def oldDiv (x y : Fin 2 → R) : Fin 2 → R :=
  ![3 * x 0 - y 1, 3 * x 1 + y 0]
def H (x : Fin 2 → R) : Fin 2 → R :=
  ![-2 * x 1, 2 * x 0]

@[implicit_reducible] def division : Magma (Carrier 2 R) :=
  FoldedExtensions.extension oldDiv H

section Field
variable {K : Type} [Field K]

def F (x : Fin 2 → K) : Fin 2 → K :=
  ![x 1 / 2, -x 0 / 2]

@[implicit_reducible] def source : Magma (Carrier 2 K) :=
  FoldedExtensions.extension oldOp F

theorem isDivision (h2 : (2 : K) ≠ 0) :
    IsDivision .left (source (K := K)) division := by
  apply extension_division
  · constructor <;> intro x y <;> ext i <;> fin_cases i <;> simp [oldOp, oldDiv]
  · intro x; ext i; fin_cases i <;> simp [F, H] <;> try field_simp [h2]
  · intro x; ext i; fin_cases i <;> simp [F, H] <;> try field_simp [h2]

theorem equation473 (h2 : (2 : K) ≠ 0) : @Equation473 _ (source (K := K)) := by
  rintro (_ | x) (_ | y)
  · rfl
  · rfl
  · change some x = some (F (oldOp x (F (oldOp x x))))
    congr 1
    ext i; fin_cases i <;> simp [F, oldOp] <;> try field_simp [h2]
    all_goals ring
  · change some x = some (oldOp y (oldOp x (oldOp y (oldOp x x))))
    congr 1
    ext i; fin_cases i <;> simp [oldOp] <;> ring

end Field

theorem reduce_op (n : Nat) (x y : Carrier 2 Int) :
    reduce n ((division (R := Int)).op x y) =
      (division (R := ZMod n)).op (reduce n x) (reduce n y) := by
  cases x <;> cases y
  all_goals first
    | rfl
    | apply congrArg some; funext i; fin_cases i <;> simp [AffineImage.reduce, oldDiv, H]

theorem bad_reduction : ¬ IsSideQuasigroup .left (division (R := ZMod 2)) := by
  intro h
  have he := (h none).1 (a₁ := some ![0, 0]) (a₂ := some ![0, 1])
    (by decide)
  have hh := congrFun (Option.some.inj he) 1
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

end Parastrophes.Eq473ImageObstruction

namespace Parastrophes.Catalogue

/-- Odd-prime Gaussian division models force every common identity on a
five-element reduction whose exceptional row is constant. -/
@[parastrophe_result] theorem left_noSingleEquation473_fin :
    ¬ SingleEquation .fin Law473 .left := by
  apply OptionReductionImage.obstruction Eq473ImageObstruction.division
    (fun n => Eq473ImageObstruction.division (R := ZMod n)) Eq473ImageObstruction.reduce_op
  · intro p hp hp2
    letI : Fact p.Prime := ⟨hp⟩
    have h2 : (2 : ZMod p) ≠ 0 := ReductionImage.two_ne_zero hp2
    exact ⟨Eq473ImageObstruction.source,
      (@Law473.models_iff _ (Eq473ImageObstruction.source (K := ZMod p))).mpr (Eq473ImageObstruction.equation473 h2),
      Eq473ImageObstruction.isDivision h2⟩
  · exact Eq473ImageObstruction.bad_reduction

end Parastrophes.Catalogue
