
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,0],[1,0,0],[2,1,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,0],[1,0,0],[2,1,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,0,0],[2,1,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,0],[1,0,0],[2,1,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [1245, 1259] [107, 108, 846, 1224, 1251, 4598] :=
    ⟨Fin 3, «All4x4Tables [[0,0,0],[1,0,0],[2,1,2]]», Finite.of_fintype _, by decideFin!⟩
