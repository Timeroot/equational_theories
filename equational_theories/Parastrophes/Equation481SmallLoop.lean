import equational_theories.Parastrophes.CrossInverseLoopExtensions
import Mathlib.Data.Fin.VecNotation

/-!
# A small test model outside the central loop towers

This seven-element cross-inverse loop was found by Mace4. Its inverse has a
five-cycle and fixes a nonunit element. The previously used central towers
have only even nontrivial inverse cycles and one fixed point, so those towers
miss this behaviour even at very large orders.

The Cartesian-square construction gives a 49-element E481 left-division
image. It refutes the eleven-operation proposal
`x = f³(f(x) * (x * f⁵(x)))`, where `f(x)=e*x` and e is the right identity.
The proposal survived all tested central towers, including random choices of
their free offsets. This is a refutation of this particular term, not a
negative answer to the single-equation or uniform-term questions.

Only the seven-element loop is tabulated. The image-membership proof uses
the general Cartesian-square construction; no 49-by-49 table is required.
-/
namespace Parastrophes.Eq481SmallLoop
open CrossInverseLoopExtensions

@[implicit_reducible] def multiplication : Magma (Fin 7) := ⟨fun x y =>
  (![![0,1,2,3,4,5,6],
     ![1,3,0,5,2,6,4],
     ![2,6,4,0,5,1,3],
     ![3,4,1,6,0,2,5],
     ![4,5,6,2,1,3,0],
     ![5,2,3,4,6,0,1],
     ![6,0,5,1,3,4,2]] : Fin 7 → Fin 7 → Fin 7) x y⟩

def inverse : Fin 7 ≃ Fin 7 where
  toFun := ![0,2,3,4,6,5,1]
  invFun := ![0,6,1,2,3,5,4]
  left_inv := by decide
  right_inv := by decide

def loop : CIPLoop (Fin 7) where
  magma := multiplication
  unit := 0
  inverse := inverse
  quasigroup := by
    have hr : ∀ x, Function.Injective (multiplication.op x) := by decide
    have hc : ∀ y, Function.Injective (fun x => multiplication.op x y) := by decide
    constructor
    · intro x
      exact ⟨hr x, Finite.surjective_of_injective (hr x)⟩
    · intro x
      exact ⟨hc x, Finite.surjective_of_injective (hc x)⟩
  unit_left := by decide
  unit_right := by decide
  cross := by decide

theorem inverse_five_cycle :
    inverse 1 = 2 ∧ inverse 2 = 3 ∧ inverse 3 = 4 ∧
      inverse 4 = 6 ∧ inverse 6 = 1 := by decide

theorem inverse_nonunit_fixed : inverse 5 = 5 ∧ (5 : Fin 7) ≠ loop.unit := by decide

@[implicit_reducible] def division : Magma (Fin 7 × Fin 7) := loop.division

theorem division_inImage : InImage Law481 .left division := loop.division_inImage

/-- Counted with e as a constant: three outer f applications, two products,
one f on the left and five f applications on the right give eleven operations. -/
def candidate {A : Type} (D : Magma A) (e x : A) : A :=
  let f := D.op e
  f (f (f (D.op (f x) (D.op x (f (f (f (f (f x)))))))))

theorem candidate_fails : candidate division (0,0) (0,1) ≠ (0,1) := by decide

end Parastrophes.Eq481SmallLoop
