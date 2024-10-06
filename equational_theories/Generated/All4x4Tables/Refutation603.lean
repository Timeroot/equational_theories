
import equational_theories.AllEquations
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[1,8,7,1,1,7,7,8,8],[2,5,6,2,2,6,6,5,5],[3,0,4,3,3,4,4,0,0],[7,1,8,7,7,8,8,1,1],[8,7,1,8,8,1,1,7,7],[0,4,3,0,0,3,3,4,4],[4,3,0,4,4,0,0,3,3],[6,2,5,6,6,5,5,2,2],[5,6,2,5,5,2,2,6,6]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[1,8,7,1,1,7,7,8,8],[2,5,6,2,2,6,6,5,5],[3,0,4,3,3,4,4,0,0],[7,1,8,7,7,8,8,1,1],[8,7,1,8,8,1,1,7,7],[0,4,3,0,0,3,3,4,4],[4,3,0,4,4,0,0,3,3],[6,2,5,6,6,5,5,2,2],[5,6,2,5,5,2,2,6,6]]» : Magma (Fin 9) where
  op := memoFinOp fun x y => [[1,8,7,1,1,7,7,8,8],[2,5,6,2,2,6,6,5,5],[3,0,4,3,3,4,4,0,0],[7,1,8,7,7,8,8,1,1],[8,7,1,8,8,1,1,7,7],[0,4,3,0,0,3,3,4,4],[4,3,0,4,4,0,0,3,3],[6,2,5,6,6,5,5,2,2],[5,6,2,5,5,2,2,6,6]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[1,8,7,1,1,7,7,8,8],[2,5,6,2,2,6,6,5,5],[3,0,4,3,3,4,4,0,0],[7,1,8,7,7,8,8,1,1],[8,7,1,8,8,1,1,7,7],[0,4,3,0,0,3,3,4,4],[4,3,0,4,4,0,0,3,3],[6,2,5,6,6,5,5,2,2],[5,6,2,5,5,2,2,6,6]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [2887] [255, 3253, 3456] :=
    ⟨Fin 9, «FinitePoly [[1,8,7,1,1,7,7,8,8],[2,5,6,2,2,6,6,5,5],[3,0,4,3,3,4,4,0,0],[7,1,8,7,7,8,8,1,1],[8,7,1,8,8,1,1,7,7],[0,4,3,0,0,3,3,4,4],[4,3,0,4,4,0,0,3,3],[6,2,5,6,6,5,5,2,2],[5,6,2,5,5,2,2,6,6]]», by decideFin!⟩