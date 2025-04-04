
import Mathlib.Data.Finite.Prod
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[0,0,2],[0,2,2],[0,0,2]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «All4x4Tables [[0,0,2],[0,2,2],[0,0,2]]» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[0,2,2],[0,0,2]]"

/-! The facts -/
@[equational_result]
theorem «Facts from All4x4Tables [[0,0,2],[0,2,2],[0,0,2]]» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [343] [3255, 3261, 3271, 3281, 3309, 3319, 3346, 3456, 3661, 3667, 3677, 3687, 3721, 3724, 3725, 3752, 3862, 4065, 4269, 4275, 4284, 4320, 4380, 4629] :=
    ⟨Fin 3, «All4x4Tables [[0,0,2],[0,2,2],[0,0,2]]», Finite.of_fintype _, by decideFin!⟩
