import equational_theories.Parastrophes.FoldedExtensions

/-! E879 has a countable idempotence-free collision model. Its old square map
is multiplication by i-1 on Gaussian integers, with an extra Boolean coordinate.
A left inverse of that square map gives the new, noninjective row. -/
namespace Parastrophes.GaussianFold
open FoldedExtensions

abbrev Pair := Int × Int

def rot (x : Pair) : Pair := (-x.2, x.1)
def square (x : Pair) : Pair := (-x.1 - x.2, x.1 - x.2)

/-- Division by i-1, rounding off the image of the square map. -/
def halve (x : Pair) : Pair := ((x.2 - x.1) / 2, -((x.1 + x.2) / 2))

theorem halve_square (x : Pair) : halve (square x) = x := by
  ext <;> simp only [halve, square] <;> omega

abbrev Carrier := Bool × Pair

def oldOp (x y : Carrier) : Carrier :=
  (y.1, (-x.2.1 - y.2.2, -x.2.2 + y.2.1))

def fold : Carrier → Carrier
  | (false, x) => (true, halve x)
  | (true, x) => (false, x)

theorem fold_square (x : Carrier) : fold (fold (oldOp x x)) = x := by
  rcases x with ⟨b, x⟩
  have hs : oldOp (b, x) (b, x) = (b, square x) := by
    simp only [oldOp, square, Prod.mk.injEq, true_and]
    ring
  rw [hs]
  cases b <;> simp only [fold, halve_square]

theorem old_law : @Equation879 Carrier ⟨oldOp⟩ := by
  intro x y
  change x = oldOp y (oldOp (oldOp x y) (oldOp x x))
  rcases x with ⟨bx, x, x'⟩
  rcases y with ⟨byy, y, y'⟩
  simp only [oldOp, Prod.mk.injEq, true_and]
  constructor <;> ring

@[implicit_reducible] def model : Magma (Option Carrier) := extension oldOp fold

theorem model_law : @Equation879 (Option Carrier) model := by
  rintro (_ | x) (_ | y)
  · rfl
  · rfl
  · exact congrArg some (fold_square x).symm
  · exact congrArg some (old_law x y)

end GaussianFold
open GaussianFold Law

/-- The new row identifies (false,0) and (false,i), because rounded division
by i-1 sends both Gaussian integers to zero. -/
@[parastrophe_result] theorem Catalogue.not_leftQuasigroup879_all :
    ¬ SideQuasigroupLaw .all Law879 .left := by
  intro h
  have hq := h (Option Carrier) model trivial
    ((@Law879.models_iff _ model).mpr model_law)
  have hc : model.op none (some (false, 0, 0)) = model.op none (some (false, 0, 1)) := by
    decide
  have he := (hq none).1 hc
  cases he

end Parastrophes
