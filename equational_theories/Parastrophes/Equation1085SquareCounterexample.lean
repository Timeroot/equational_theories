import equational_theories.Parastrophes.Equation1085ImageCriterion
import Mathlib.Data.Fin.VecNotation

/-! Seven- and nine-element counterexamples to three square-recovery
guesses tested on 4 November. These rule out only those terms.
The source laws, inverse relations, and failed recoveries are checked by the
kernel; neither Mace4 nor the SAT solver is trusted. -/
namespace Parastrophes.Eq1085Image.SquareCounterexample

@[implicit_reducible] def source : Magma (Fin 7) := ⟨![
  ![2,0,3,1,5,4,6], ![0,3,6,4,5,1,2], ![3,4,6,2,1,5,0],
  ![1,4,2,0,3,6,5], ![2,5,0,3,1,6,4], ![3,1,5,0,6,4,2],
  ![6,3,0,1,4,2,5]]⟩

@[implicit_reducible] def divided : Magma (Fin 7) := ⟨![
  ![1,3,0,2,5,4,6], ![0,5,6,1,3,4,2], ![6,4,3,0,1,5,2],
  ![3,0,2,4,1,6,5], ![2,4,0,3,6,1,5], ![3,1,6,0,5,2,4],
  ![2,3,5,1,4,6,0]]⟩

theorem source_law : @Equation1085 (Fin 7) source := by decide

theorem divided_relation : IsDivision .left source divided := by
  change (∀ x y, source.op x (divided.op x y) = y) ∧
    (∀ x y, divided.op x (source.op x y) = y)
  decide

theorem inImage : InImage Law1085 .left divided :=
  ⟨source, (@Law1085.models_iff _ source).mpr source_law, divided_relation⟩

def recovery {G : Type} (D : Magma G) (x : G) : G :=
  D.op (D.op (D.op (D.op x (D.op x x)) x) x)
    (D.op (D.op x x) (D.op x x))

theorem failed_square : recovery divided 0 ≠ source.op 0 0 := by decide

/-- Equivalently, the proposed recovered square does not divide back to x.
This formulation also applies to searches carrying only the division table. -/
theorem failed_diagonal : divided.op 0 (recovery divided 0) ≠ 0 := by decide

/-- The other eight-operation guess. Bounded searches found no counterexample
through order eight; the certified counterexample below has order nine. -/
def recoveryOther {G : Type} (D : Magma G) (x : G) : G :=
  let s := D.op x x
  let a := D.op x s
  D.op (D.op (D.op a x) s) a

namespace Nine

@[implicit_reducible] def source : Magma (Fin 9) := ⟨![
  ![8,0,1,3,6,7,2,5,4],
  ![0,2,1,4,3,7,6,5,8],
  ![8,7,5,6,0,2,3,1,4],
  ![3,2,1,6,4,7,8,5,0],
  ![1,2,6,4,0,7,3,5,8],
  ![0,2,1,3,4,7,8,5,6],
  ![0,2,1,8,3,7,4,5,6],
  ![4,7,5,6,8,2,3,1,0],
  ![4,2,1,0,8,7,6,5,3]]⟩

@[implicit_reducible] def divided : Magma (Fin 9) := ⟨![
  ![1,2,6,3,8,7,4,5,0],
  ![0,2,1,4,3,7,6,5,8],
  ![4,7,5,6,8,2,3,1,0],
  ![8,2,1,0,4,7,3,5,6],
  ![4,0,1,6,3,7,2,5,8],
  ![0,2,1,3,4,7,8,5,6],
  ![0,2,1,4,6,7,8,5,3],
  ![8,7,5,6,0,2,3,1,4],
  ![3,2,1,8,0,7,6,5,4]]⟩

theorem source_law : @Equation1085 (Fin 9) source := by decide

theorem divided_relation : IsDivision .left source divided := by
  change (∀ x y, source.op x (divided.op x y) = y) ∧
    (∀ x y, divided.op x (source.op x y) = y)
  decide

theorem inImage : InImage Law1085 .left divided :=
  ⟨source, (@Law1085.models_iff _ source).mpr source_law, divided_relation⟩

theorem failed_square : recoveryOther divided 0 ≠ source.op 0 0 := by decide

end Nine

namespace Third

/-- The eighteen-operation successor to the two eight-operation guesses. -/
def recovery {G : Type} (D : Magma G) (x : G) : G :=
  let s := D.op x x
  let a := D.op s x
  D.op (D.op s (D.op (D.op (D.op s a) x) s))
    (D.op (D.op s (D.op (D.op x s) x)) a)

@[implicit_reducible] def source : Magma (Fin 9) := ⟨![
  ![8,0,6,4,3,5,1,2,7], ![0,4,7,3,1,8,6,5,2], ![0,6,7,4,3,8,1,5,2],
  ![0,4,8,6,1,7,3,2,5], ![5,4,7,6,1,2,3,8,0], ![5,6,8,4,3,2,1,7,0],
  ![8,4,5,6,1,0,3,2,7], ![1,6,5,4,3,7,2,0,8], ![7,6,2,4,3,0,1,8,5]]⟩

@[implicit_reducible] def divided : Magma (Fin 9) := ⟨![
  ![1,6,7,4,3,5,2,8,0], ![0,4,8,3,1,7,6,2,5], ![0,6,8,4,3,7,1,2,5],
  ![0,4,7,6,1,8,3,5,2], ![8,4,5,6,1,0,3,2,7], ![8,6,5,4,3,0,1,7,2],
  ![5,4,7,6,1,2,3,8,0], ![7,0,6,4,3,2,1,5,8], ![5,6,2,4,3,8,1,0,7]]⟩

theorem source_law : @Equation1085 (Fin 9) source := by decide

theorem divided_relation : IsDivision .left source divided := by
  change (∀ x y, source.op x (divided.op x y) = y) ∧
    (∀ x y, divided.op x (source.op x y) = y)
  decide

theorem inImage : InImage Law1085 .left divided :=
  ⟨source, (@Law1085.models_iff _ source).mpr source_law, divided_relation⟩

theorem failed_square : recovery divided 0 ≠ source.op 0 0 := by decide

/-- Although source squaring is bijective, division's square map need not be. -/
theorem divided_square_not_injective : ¬ Function.Injective (fun x => divided.op x x) := by
  intro hi
  have he := hi (a₁ := 0) (a₂ := 4) (by decide)
  exact (by decide : (0 : Fin 9) ≠ 4) he

end Third

end Parastrophes.Eq1085Image.SquareCounterexample
