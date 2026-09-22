import equational_theories.Spectrum.Basic
import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic

/-! # Recovering a Boolean-group operation from E898

Each equation below is checked in Lean from the E898 hypothesis. The proof
replays a first-order derivation; no external prover result is trusted.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Spectrum.BooleanReduction
variable {G : Type*} [Magma G]

def op (a x y : G) : G := ((a ◇ x) ◇ (y ◇ a)) ◇ a

/-- The parameterized operation satisfies the Boolean-group law E895. -/
theorem law (h : Equation898 G) (a x y z : G) :
    x = op a y (op a (op a x z) (op a y z)) := by
  simp only [op]
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op (Magma.op X0 X2) (Magma.op X2 X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : x ≠ (Magma.op (Magma.op (Magma.op a y) (Magma.op (Magma.op (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a x) (Magma.op z a)) a)) (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a)) a) a)) a) := by grind
  clear hlaw hn
  have eq5 : ∀ X0 X1 X2 X3 : G, (Magma.op X1 (Magma.op X0 (Magma.op (Magma.op (Magma.op X0 X3) (Magma.op X3 X2)) X1))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X2 X1 (Magma.op (Magma.op X0 X3) (Magma.op X3 X2))
       have i₂ := eq3 X0 X2 X3
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X1 (Magma.op X2 (Magma.op X0 X1))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 X2 (Magma.op X1 (Magma.op X2 (Magma.op X0 X1))) (Magma.op X0 X1)
       have i₂ := eq3 X0 (Magma.op X2 (Magma.op X0 X1)) X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 (Magma.op X2 X0)) (Magma.op X3 (Magma.op X0 (Magma.op X1 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7 (Magma.op X3 (Magma.op X0 (Magma.op X1 X3))) X1 X2
       have i₂ := eq7 X1 X3 X0
       grind)
    | exact superpose eq7 eq7
    | exact resolve eq7 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op (Magma.op X1 X2) X0) (Magma.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7 (Magma.op X0 X1) (Magma.op X1 X2) X2
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq7
    | exact resolve eq7 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11 : ∀ X0 X1 X2 X3 : G, (Magma.op X2 (Magma.op X0 (Magma.op (Magma.op X3 X1) X2))) = (Magma.op (Magma.op X1 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7 X3 X1 (Magma.op X2 (Magma.op X0 (Magma.op (Magma.op X3 X1) X2)))
       have i₂ := eq7 (Magma.op X3 X1) X2 X0
       grind)
    | exact superpose eq7 eq7
    | exact resolve eq7 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op (Magma.op X0 X4) (Magma.op X4 X3)) = (Magma.op X1 (Magma.op X2 (Magma.op (Magma.op (Magma.op X2 X3) X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5 X2 X1 (Magma.op (Magma.op X0 X4) (Magma.op X4 X3)) X3
       have i₂ := eq3 X0 X3 X4
       grind)
    | exact superpose eq3 eq5
    | exact resolve eq5 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op X1 X2) (Magma.op X2 X0)) X3) X0) X1) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7 X1 (Magma.op (Magma.op (Magma.op X1 X2) (Magma.op X2 X0)) X3) X3
       have i₂ := eq5 X1 X3 X0 X2
       grind)
    | exact superpose eq5 eq7
    | exact resolve eq7 eq5
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5
  have eq35 : ∀ X0 X2 X3 X4 : G, (Magma.op (Magma.op X0 X4) (Magma.op X4 X3)) = (Magma.op (Magma.op X0 X2) (Magma.op X2 X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq17 X0 x X2 X3 X4
       have i₂ := eq11 X2 X0 x (Magma.op X2 X3)
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq42 : ∀ X0 X1 X2 X3 : G, (Magma.op X2 X1) = (Magma.op (Magma.op X0 X3) (Magma.op X3 (Magma.op (Magma.op X1 X0) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 X3 (Magma.op (Magma.op X1 X0) X2) (Magma.op X2 X1)
       have i₂ := eq10 X2 X1 X0
       grind)
    | exact superpose eq10 eq10
    | exact resolve eq10 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op (Magma.op (Magma.op X1 X2) X3) (Magma.op (Magma.op X2 X0) X1)) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op (Magma.op X2 X0) X1) (Magma.op X1 X2) X3
       have i₂ := eq10 X1 X2 X0
       grind)
    | exact superpose eq10 eq10
    | exact resolve eq10 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op (Magma.op X1 X2) (Magma.op X3 X0)) (Magma.op (Magma.op X2 X0) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7 (Magma.op (Magma.op X2 X0) X1) (Magma.op X1 X2) X3
       have i₂ := eq10 X1 X2 X0
       grind)
    | exact superpose eq10 eq7
    | exact resolve eq7 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 X3 : G, (Magma.op X2 (Magma.op X0 X1)) = (Magma.op (Magma.op (Magma.op X1 (Magma.op X2 X3)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7 X3 (Magma.op X1 (Magma.op X2 X3)) (Magma.op X2 (Magma.op X0 X1))
       have i₂ := eq9 X1 X2 X0 X3
       grind)
    | exact superpose eq9 eq7
    | exact resolve eq7 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7 eq9
  have eq268 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X1 (Magma.op (Magma.op X2 X0) X3)) = (Magma.op (Magma.op (Magma.op (Magma.op X0 X1) X2) X4) (Magma.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10 X4 X3 (Magma.op X1 (Magma.op (Magma.op X2 X0) X3))
       have i₂ := eq11 X1 X0 X3 X2
       grind)
    | exact superpose eq11 eq10
    | exact resolve eq10 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10 eq11
  have eq1656 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op (Magma.op X3 X4) (Magma.op (Magma.op X1 (Magma.op X2 X3)) X0)) = (Magma.op (Magma.op (Magma.op X0 X1) X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq27 X4 X2 X3 (Magma.op (Magma.op X3 X4) (Magma.op (Magma.op X1 (Magma.op X2 X3)) X0))
       have i₂ := eq42 (Magma.op X2 X3) X1 X0 (Magma.op X3 X4)
       grind)
    | exact superpose eq42 eq27
    | exact resolve eq27 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq42
  have eq5135 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X0 (Magma.op (Magma.op (Magma.op X2 X3) X1) X4)) = (Magma.op (Magma.op (Magma.op (Magma.op X1 X2) (Magma.op X0 X3)) X5) (Magma.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq35 (Magma.op (Magma.op X1 X2) (Magma.op X0 X3)) X5 X4 (Magma.op (Magma.op X2 X3) X1)
       have i₂ := eq56 X3 X1 X2 X0
       grind)
    | exact superpose eq56 eq35
    | exact resolve eq35 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq56
  have eq5158 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X0 (Magma.op (Magma.op (Magma.op X2 X3) X1) X4)) = (Magma.op X2 (Magma.op (Magma.op (Magma.op X0 X3) X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5135 X0 X1 X2 X3 X4 x
       have i₂ := eq268 X1 X2 (Magma.op X0 X3) X4 x
       grind)
    | exact superpose eq268 eq5135
    | exact resolve eq5135 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq5135
  have eq7461 : x ≠ (Magma.op (Magma.op (Magma.op a y) (Magma.op (Magma.op (Magma.op (Magma.op a x) (Magma.op z a)) (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a) a)) a)) a) := by
    first
    | (have i₁ := eq4
       have i₂ := eq190 (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a) a (Magma.op (Magma.op a x) (Magma.op z a)) a
       grind)
    | exact superpose eq190 eq4
    | exact resolve eq4 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq7607 : x ≠ (Magma.op (Magma.op (Magma.op a x) (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a) a)) a)) a) := by
    first
    | (have i₁ := eq7461
       have i₂ := eq5158 (Magma.op a y) (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a) a) (Magma.op a x) (Magma.op z a) a
       grind)
    | (have i₁ := eq7461
       have i₂ := eq5158 (Magma.op a x) (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a) a) (Magma.op a y) (Magma.op z a) a
       grind)
    | exact superpose eq5158 eq7461
    | exact resolve eq7461 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158 eq7461
  have eq7703 : x ≠ (Magma.op (Magma.op (Magma.op (Magma.op a (Magma.op (Magma.op a y) (Magma.op z a))) x) (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a)) a) := by
    first
    | (have i₁ := eq7607
       have i₂ := eq1656 a (Magma.op (Magma.op a y) (Magma.op z a)) (Magma.op (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) a) a) a x
       grind)
    | exact superpose eq1656 eq7607
    | exact resolve eq7607 eq1656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1656 eq7607
  have eq7747 : False := by grind
  exact eq7747

end Spectrum.BooleanReduction
