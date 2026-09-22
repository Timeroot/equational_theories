import equational_theories.Spectrum.Basic
import equational_theories.Superposition
import equational_theories.Equations.All
import Mathlib.Tactic

/-! Algebraic identities for the Gaussian representation of E546.
Each first-order derivation is replayed by Lean; the external prover is not trusted. -/
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Spectrum.GaussianRepresentation
variable {G : Type*} [Magma G]

def addOp (a x y : G) : G := (x ◇ a) ◇ (a ◇ (y ◇ (a ◇ a)))
def turn (a x : G) : G := ((a ◇ a) ◇ (a ◇ a)) ◇ x

theorem comm (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) = (Magma.op (Magma.op y a) (Magma.op a (Magma.op x (Magma.op a a)))) := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) ≠ (Magma.op (Magma.op y a) (Magma.op a (Magma.op x (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 X1)) = (Magma.op X1 (Magma.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 (Magma.op X1 (Magma.op X2 X0)) X0 X2
       have i₂ := eq7 (Magma.op X2 X0) X1
       grind)
    | exact superpose eq7 eq3
    | exact resolve eq3 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq118 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X1 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 X0) X3 X2
       have i₂ := eq10 X2 X0 X1
       grind)
    | (have i₁ := eq10 (Magma.op X1 X0) X3 X2
       have i₂ := eq10 X0 X2 X1
       grind)
    | exact superpose eq10 eq10
    | exact resolve eq10 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) ≠ (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a x)))) := by
    first
    | (have i₁ := eq4
       have i₂ := eq10 x a a
       grind)
    | (have i₁ := eq4
       have i₂ := eq10 a x a
       grind)
    | exact superpose eq10 eq4
    | exact resolve eq4 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a x)))) ≠ (Magma.op (Magma.op x a) (Magma.op a (Magma.op a (Magma.op a y)))) := by
    first
    | (have i₁ := eq156
       have i₂ := eq10 y a a
       grind)
    | (have i₁ := eq156
       have i₂ := eq10 a y a
       grind)
    | exact superpose eq10 eq156
    | exact resolve eq156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq169 : (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a x)))) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op a y) (Magma.op x a))) := by
    first
    | (have i₁ := eq157
       have i₂ := eq118 a a (Magma.op a y) (Magma.op x a)
       grind)
    | exact superpose eq118 eq157
    | exact resolve eq157 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq173 : (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a x)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op a y)))) := by
    first
    | (have i₁ := eq169
       have i₂ := eq10 (Magma.op a y) a x
       grind)
    | (have i₁ := eq169
       have i₂ := eq10 a (Magma.op a y) x
       grind)
    | exact superpose eq10 eq169
    | exact resolve eq169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq177 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op a y)))) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op a x) (Magma.op y a))) := by
    first
    | (have i₁ := eq173
       have i₂ := eq118 a a (Magma.op a x) (Magma.op y a)
       grind)
    | exact superpose eq118 eq173
    | exact resolve eq173 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq173
  have eq181 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op a y)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op y (Magma.op a x)))) := by
    first
    | (have i₁ := eq177
       have i₂ := eq10 (Magma.op a x) a y
       grind)
    | (have i₁ := eq177
       have i₂ := eq10 a (Magma.op a x) y
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op a y)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op a y)))) := by
    first
    | (have i₁ := eq181
       have i₂ := eq10 y x a
       grind)
    | (have i₁ := eq181
       have i₂ := eq10 x y a
       grind)
    | exact superpose eq10 eq181
    | exact resolve eq181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10 eq181
  have eq184 : False := by grind
  exact eq184

theorem assoc (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op z (Magma.op a a)))) = (Magma.op (Magma.op x a) (Magma.op a (Magma.op (Magma.op (Magma.op y a) (Magma.op a (Magma.op z (Magma.op a a)))) (Magma.op a a)))) := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op z (Magma.op a a)))) ≠ (Magma.op (Magma.op x a) (Magma.op a (Magma.op (Magma.op (Magma.op y a) (Magma.op a (Magma.op z (Magma.op a a)))) (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq5 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 (Magma.op X0 (Magma.op X1 X2))) (Magma.op X2 (Magma.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X3 (Magma.op X1 (Magma.op X0 (Magma.op X1 X2))) X2
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X0 (Magma.op X1 X2)) (Magma.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 X2 (Magma.op X0 (Magma.op X1 X2)) X1
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1))) X1
       have i₂ := eq3 X0 X1 X2
       grind)
    | exact superpose eq3 eq7
    | exact resolve eq7 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 X1)) = (Magma.op X1 (Magma.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 (Magma.op X1 (Magma.op X2 X0)) X0 X2
       have i₂ := eq7 (Magma.op X2 X0) X1
       grind)
    | exact superpose eq7 eq3
    | exact resolve eq3 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X1 (Magma.op X0 X1) X2
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq6
    | exact resolve eq6 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) X3)) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (Magma.op X1 X2) (Magma.op X2 (Magma.op X1 X0)) X3
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq6
    | exact resolve eq6 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) (Magma.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X3 (Magma.op X1 X2) (Magma.op X2 (Magma.op X1 X0))
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq3
    | exact resolve eq3 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op X0 (Magma.op X3 (Magma.op X2 (Magma.op X1 X0))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X2 X3
       have i₂ := eq10 (Magma.op X2 (Magma.op X1 X0)) X0 X3
       grind)
    | (have i₁ := eq21 X0 X1 X2 X3
       have i₂ := eq10 X0 (Magma.op X2 (Magma.op X1 X0)) X3
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq116 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 X0) = (Magma.op (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) (Magma.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) X3 X2
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq10
    | exact resolve eq10 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X1 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 X0) X3 X2
       have i₂ := eq10 X2 X0 X1
       grind)
    | (have i₁ := eq10 (Magma.op X1 X0) X3 X2
       have i₂ := eq10 X0 X2 X1
       grind)
    | exact superpose eq10 eq10
    | exact resolve eq10 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (Magma.op X2 X0) = (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2 (Magma.op X0 X1)
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq10
    | exact resolve eq10 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq120 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 X0) = (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 X2) X3 (Magma.op X2 (Magma.op X1 X0))
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq10
    | exact resolve eq10 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10
  have eq240 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 X1)) = (Magma.op (Magma.op (Magma.op X1 (Magma.op X2 X3)) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 (Magma.op X1 (Magma.op X2 X3)) (Magma.op X3 (Magma.op X0 X1))
       have i₂ := eq5 X1 X2 X3 X0
       grind)
    | exact superpose eq5 eq18
    | exact resolve eq18 eq5
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5
  have eq241 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op X0 (Magma.op X3 (Magma.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X1 (Magma.op X3 (Magma.op X0 (Magma.op X3 (Magma.op X2 X1))))
       have i₂ := eq3 X0 (Magma.op X2 X1) X3
       grind)
    | exact superpose eq3 eq18
    | exact resolve eq18 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op (Magma.op X2 X1) (Magma.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X1 (Magma.op X3 (Magma.op (Magma.op X2 X1) (Magma.op X3 X0)))
       have i₂ := eq8 (Magma.op X2 X1) X0 X3
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq568 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op (Magma.op (Magma.op X1 X2) X0) X3) = (Magma.op X4 (Magma.op (Magma.op X2 (Magma.op X1 X3)) (Magma.op X4 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X1 X2 (Magma.op X4 (Magma.op (Magma.op X2 (Magma.op X1 X3)) (Magma.op X4 X0)))
       have i₂ := eq8 (Magma.op X2 (Magma.op X1 X3)) X0 X4
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8
  have eq571 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op (Magma.op X1 (Magma.op X3 (Magma.op X2 X4))) X0) = (Magma.op (Magma.op (Magma.op X2 X3) (Magma.op X0 X1)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X4 X2 X3 (Magma.op (Magma.op X1 (Magma.op X3 (Magma.op X2 X4))) X0)
       have i₂ := eq119 X1 (Magma.op X3 (Magma.op X2 X4)) X0
       grind)
    | exact superpose eq119 eq19
    | exact resolve eq19 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq633 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op (Magma.op X1 X2) X0) X3) = (Magma.op (Magma.op (Magma.op X1 X3) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq568 X0 X1 X2 X3 x
       have i₂ := eq242 X0 (Magma.op X1 X3) X2 x
       grind)
    | exact superpose eq242 eq568
    | exact resolve eq568 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq759 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X3) (Magma.op X2 X0)) = (Magma.op (Magma.op X1 X2) (Magma.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 X1 X3 (Magma.op (Magma.op X1 X2) (Magma.op X3 X0))
       have i₂ := eq6 (Magma.op X1 X2) X3 X0
       grind)
    | exact superpose eq6 eq22
    | exact resolve eq22 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 X1 X2 X3 : G, (Magma.op X0 (Magma.op X2 (Magma.op X1 X3))) = (Magma.op X0 (Magma.op X3 (Magma.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (Magma.op X1 X3) X2 (Magma.op X0 (Magma.op X3 (Magma.op X1 X2)))
       have i₂ := eq22 X2 X1 X3 X0
       grind)
    | exact superpose eq22 eq6
    | exact resolve eq6 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6
  have eq7504 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X1 X3) X0)) = (Magma.op (Magma.op X3 (Magma.op X4 (Magma.op X0 X1))) (Magma.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 (Magma.op (Magma.op X1 X3) X0) X3 X4 X2
       have i₂ := eq119 X1 X3 X0
       grind)
    | exact superpose eq119 eq116
    | exact resolve eq116 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7536 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X1 (Magma.op X0 (Magma.op X2 (Magma.op X3 X4)))) = (Magma.op (Magma.op X4 X0) (Magma.op (Magma.op X3 X2) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 (Magma.op X0 (Magma.op X2 (Magma.op X3 X4))) X4 (Magma.op X3 X2) X1
       have i₂ := eq22 X4 X3 X2 X0
       grind)
    | exact superpose eq22 eq116
    | exact resolve eq116 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq116
  have eq7859 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X1 X3) X0)) = (Magma.op (Magma.op X3 X4) (Magma.op (Magma.op X4 (Magma.op X0 X1)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7504 X0 X1 X2 X3 X4
       have i₂ := eq759 X2 X3 X4 (Magma.op X4 (Magma.op X0 X1))
       grind)
    | (have i₁ := eq7504 X0 X1 X2 X3 X4
       have i₂ := eq759 X2 X3 (Magma.op X4 (Magma.op X0 X1)) X4
       grind)
    | exact superpose eq759 eq7504
    | exact resolve eq7504 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504
  have eq12726 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X2 (Magma.op (Magma.op X3 (Magma.op X4 X1)) X0)) = (Magma.op (Magma.op (Magma.op X4 X3) X5) (Magma.op (Magma.op X5 (Magma.op X0 X1)) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq120 (Magma.op (Magma.op X3 (Magma.op X4 X1)) X0) (Magma.op X4 X3) X5 X2
       have i₂ := eq120 X1 X4 X3 X0
       grind)
    | exact superpose eq120 eq120
    | exact resolve eq120 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq13101 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X3 (Magma.op X4 X1)) X0)) = (Magma.op X2 (Magma.op (Magma.op X1 (Magma.op X4 X3)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12726 X0 X1 X2 X3 X4 x
       have i₂ := eq7859 X0 X1 X2 (Magma.op X4 X3) x
       grind)
    | exact superpose eq7859 eq12726
    | exact resolve eq12726 eq7859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12726
  have eq13686 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X5 (Magma.op (Magma.op X1 (Magma.op X0 X2)) X3)) = (Magma.op (Magma.op (Magma.op X0 X1) (Magma.op X2 (Magma.op X3 (Magma.op X4 X5)))) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq240 (Magma.op X1 (Magma.op X0 X2)) X3 X4 X5
       have i₂ := eq118 X1 X0 X2 (Magma.op X3 (Magma.op X4 X5))
       grind)
    | (have i₁ := eq240 (Magma.op X2 X3) X1 X2 X3
       have i₂ := eq118 (Magma.op X2 X3) X1 X2 X3
       grind)
    | exact superpose eq118 eq240
    | exact resolve eq240 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13781 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X3 (Magma.op (Magma.op X2 (Magma.op X4 X0)) X1)) = (Magma.op X4 (Magma.op (Magma.op X0 (Magma.op X1 X2)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq119 (Magma.op (Magma.op X2 (Magma.op X4 X0)) X1) X4 X3
       have i₂ := eq240 X1 X2 X4 X0
       grind)
    | exact superpose eq240 eq119
    | exact resolve eq119 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq240
  have eq13932 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X5 (Magma.op (Magma.op X1 (Magma.op X0 X2)) X3)) = (Magma.op (Magma.op (Magma.op X3 X2) (Magma.op X4 (Magma.op X0 X1))) (Magma.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq13686 X0 X1 X2 X3 X4 X5
       have i₂ := eq571 X4 (Magma.op X0 X1) X3 X2 (Magma.op X4 X5)
       grind)
    | (have i₁ := eq13686 X2 X3 X0 X3 X4 X5
       have i₂ := eq571 X0 (Magma.op X3 (Magma.op X4 X5)) X2 X3 X4
       grind)
    | exact superpose eq571 eq13686
    | exact resolve eq13686 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq13686
  have eq14098 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X5 (Magma.op (Magma.op X1 (Magma.op X0 X2)) X3)) = (Magma.op (Magma.op (Magma.op X3 X2) X4) (Magma.op (Magma.op X4 (Magma.op X0 X1)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq13932 X0 X1 X2 X3 X4 X5
       have i₂ := eq759 X5 (Magma.op X3 X2) X4 (Magma.op X4 (Magma.op X0 X1))
       grind)
    | (have i₁ := eq13932 X0 X1 X2 X3 X4 X5
       have i₂ := eq759 X5 (Magma.op X3 X2) (Magma.op X4 (Magma.op X0 X1)) X4
       grind)
    | exact superpose eq759 eq13932
    | exact resolve eq13932 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13932
  have eq14196 : ∀ X0 X1 X2 X3 X5 : G, (Magma.op X5 (Magma.op (Magma.op X1 (Magma.op X0 X2)) X3)) = (Magma.op X5 (Magma.op (Magma.op X1 (Magma.op X3 X2)) X0)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14098 X0 X1 X2 X3 x X5
       have i₂ := eq7859 X0 X1 X5 (Magma.op X3 X2) x
       grind)
    | exact superpose eq7859 eq14098
    | exact resolve eq14098 eq7859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7859 eq14098
  have eq14461 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op (Magma.op (Magma.op X3 (Magma.op X2 X0)) X4) X1) = (Magma.op X3 (Magma.op X4 (Magma.op (Magma.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq241 X4 (Magma.op X3 (Magma.op X2 X0)) X1 X3
       have i₂ := eq241 X1 X0 X2 X3
       grind)
    | exact superpose eq241 eq241
    | exact resolve eq241 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14648 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X3 (Magma.op X4 (Magma.op (Magma.op X0 X1) X2))) = (Magma.op (Magma.op X5 X4) (Magma.op (Magma.op X1 (Magma.op X5 (Magma.op X2 X0))) X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq118 X4 X5 (Magma.op X1 (Magma.op X5 (Magma.op X2 X0))) X3
       have i₂ := eq241 X1 X0 X2 X5
       grind)
    | exact superpose eq241 eq118
    | exact resolve eq118 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14701 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X3 (Magma.op X4 (Magma.op (Magma.op X0 X1) X2))) = (Magma.op X5 (Magma.op (Magma.op (Magma.op X2 X0) (Magma.op X3 X1)) (Magma.op X5 X4))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14648 X0 X1 X2 X3 X4 X5
       have i₂ := eq13781 (Magma.op X2 X0) X3 X1 (Magma.op X5 X4) X5
       grind)
    | (have i₁ := eq14648 X0 X0 X2 X3 X4 X1
       have i₂ := eq13781 X0 X1 (Magma.op X2 X0) X3 (Magma.op X1 X4)
       grind)
    | exact superpose eq13781 eq14648
    | exact resolve eq14648 eq13781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14648
  have eq14876 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op (Magma.op (Magma.op X3 X1) X4) (Magma.op X2 X0)) = (Magma.op X3 (Magma.op X4 (Magma.op (Magma.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14701 X0 X1 X2 X3 X4 x
       have i₂ := eq242 X4 (Magma.op X3 X1) (Magma.op X2 X0) x
       grind)
    | exact superpose eq242 eq14701
    | exact resolve eq14701 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq14701
  have eq20881 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op (Magma.op X3 X4) (Magma.op X5 (Magma.op X1 (Magma.op X4 (Magma.op X2 X0))))) = (Magma.op (Magma.op X3 X5) (Magma.op (Magma.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq759 (Magma.op X1 (Magma.op X4 (Magma.op X2 X0))) X3 X5 X4
       have i₂ := eq241 X1 X0 X2 X4
       grind)
    | exact superpose eq241 eq759
    | exact resolve eq759 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq759
  have eq23248 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X4 (Magma.op X0 (Magma.op X3 (Magma.op X2 X1)))) = (Magma.op X4 (Magma.op X0 (Magma.op X1 (Magma.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq783 X4 X3 X0 (Magma.op X2 X1)
       have i₂ := eq118 X1 X2 X3 X0
       grind)
    | (have i₁ := eq783 X0 X0 (Magma.op X1 X2) X3
       have i₂ := eq118 X0 X1 X2 X3
       grind)
    | exact superpose eq118 eq783
    | exact resolve eq783 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq23654 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op (Magma.op (Magma.op X0 X1) X2) (Magma.op X3 (Magma.op X4 X5))) = (Magma.op (Magma.op (Magma.op X0 (Magma.op X5 (Magma.op X4 X3))) X2) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq633 X2 X0 X1 (Magma.op X5 (Magma.op X4 X3))
       have i₂ := eq783 (Magma.op (Magma.op X0 X1) X2) X4 X5 X3
       grind)
    | (have i₁ := eq633 X2 X0 X1 (Magma.op X5 (Magma.op X4 X3))
       have i₂ := eq783 (Magma.op (Magma.op X0 X1) X2) X4 X3 X5
       grind)
    | exact superpose eq783 eq633
    | exact resolve eq633 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq23656 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op x a) (Magma.op a (Magma.op (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a z)))) (Magma.op a a)))) := by
    first
    | (have i₁ := eq4
       have i₂ := eq783 a a z a
       grind)
    | (have i₁ := eq4
       have i₂ := eq783 a a a z
       grind)
    | exact superpose eq783 eq4
    | exact resolve eq4 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23657 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op a (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a z))))) (Magma.op x a))) := by
    first
    | (have i₁ := eq23656
       have i₂ := eq7536 a (Magma.op x a) (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a z)))) a a
       grind)
    | exact superpose eq7536 eq23656
    | exact resolve eq23656 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23656
  have eq23659 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op (Magma.op (Magma.op X0 X1) X2) (Magma.op X3 (Magma.op X4 X5))) = (Magma.op X0 (Magma.op X2 (Magma.op (Magma.op (Magma.op X4 X3) X1) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23654 X0 X1 X2 X3 X4 X5
       have i₂ := eq14461 (Magma.op X4 X3) X1 X5 X0 X2
       grind)
    | exact superpose eq14461 eq23654
    | exact resolve eq23654 eq14461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14461 eq23654
  have eq24049 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op a (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a z)))))))) := by
    first
    | (have i₁ := eq23657
       have i₂ := eq783 (Magma.op a a) x (Magma.op a (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a z))))) a
       grind)
    | (have i₁ := eq23657
       have i₂ := eq783 (Magma.op a a) x a (Magma.op a (Magma.op (Magma.op y a) (Magma.op a (Magma.op a (Magma.op a z)))))
       grind)
    | exact superpose eq783 eq23657
    | exact resolve eq23657 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23657
  have eq24051 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X0 (Magma.op X2 (Magma.op (Magma.op (Magma.op X4 X3) X1) X5))) = (Magma.op X0 (Magma.op X2 (Magma.op (Magma.op (Magma.op X4 X5) X1) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23659 X0 X1 X2 X5 X4 X3
       have i₂ := eq14876 (Magma.op X4 X3) X1 X5 X0 X2
       grind)
    | (have i₁ := eq23659 X0 X1 X2 X4 (Magma.op X0 X1) X2
       have i₂ := eq14876 X0 X1 X2 (Magma.op (Magma.op X0 X1) X2) X4
       grind)
    | exact superpose eq14876 eq23659
    | exact resolve eq23659 eq14876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14876 eq23659
  have eq24365 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op (Magma.op a (Magma.op a (Magma.op a z))) x) (Magma.op y a))) := by
    first
    | (have i₁ := eq24049
       have i₂ := eq20881 (Magma.op a (Magma.op a (Magma.op a z))) x (Magma.op y a) a a a
       grind)
    | exact superpose eq20881 eq24049
    | exact resolve eq24049 eq20881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24049
  have eq24591 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op y (Magma.op (Magma.op a (Magma.op a (Magma.op a z))) x)))) := by
    first
    | (have i₁ := eq24365
       have i₂ := eq783 (Magma.op a a) y (Magma.op (Magma.op a (Magma.op a (Magma.op a z))) x) a
       grind)
    | (have i₁ := eq24365
       have i₂ := eq783 (Magma.op a a) y a (Magma.op (Magma.op a (Magma.op a (Magma.op a z))) x)
       grind)
    | exact superpose eq783 eq24365
    | exact resolve eq24365 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24365
  have eq24775 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op (Magma.op a (Magma.op a (Magma.op a z))) y)))) := by
    first
    | (have i₁ := eq24591
       have i₂ := eq23248 a x (Magma.op a (Magma.op a (Magma.op a z))) y (Magma.op a a)
       grind)
    | (have i₁ := eq24591
       have i₂ := eq23248 a y (Magma.op a (Magma.op a (Magma.op a z))) x (Magma.op a a)
       grind)
    | exact superpose eq23248 eq24591
    | exact resolve eq24591 eq23248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23248 eq24591
  have eq24921 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op a z) (Magma.op y a)) x)))) := by
    first
    | (have i₁ := eq24775
       have i₂ := eq13781 (Magma.op a z) y a x a
       grind)
    | (have i₁ := eq24775
       have i₂ := eq13781 a a (Magma.op a z) y x
       grind)
    | exact superpose eq13781 eq24775
    | exact resolve eq24775 eq13781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24775
  have eq25033 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op a x) (Magma.op y a)) z)))) := by
    first
    | (have i₁ := eq24921
       have i₂ := eq24051 a (Magma.op y a) a z a x
       grind)
    | (have i₁ := eq24921
       have i₂ := eq24051 a (Magma.op y a) a x a z
       grind)
    | exact superpose eq24051 eq24921
    | exact resolve eq24921 eq24051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24921
  have eq25109 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op y (Magma.op a x))) z)))) := by
    first
    | (have i₁ := eq25033
       have i₂ := eq13101 z a a (Magma.op a x) y
       grind)
    | (have i₁ := eq25033
       have i₂ := eq13101 z (Magma.op a x) a a y
       grind)
    | exact superpose eq13101 eq25033
    | exact resolve eq25033 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25033
  have eq25155 : (Magma.op (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) (Magma.op a (Magma.op a (Magma.op a z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25109
       have i₂ := eq783 a a y x
       grind)
    | (have i₁ := eq25109
       have i₂ := eq783 a a x y
       grind)
    | exact superpose eq783 eq25109
    | exact resolve eq25109 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25109
  have eq25187 : (Magma.op (Magma.op z a) (Magma.op (Magma.op a a) (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25155
       have i₂ := eq7536 a (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a) a a z
       grind)
    | exact superpose eq7536 eq25155
    | exact resolve eq25155 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25155
  have eq25201 : (Magma.op (Magma.op z a) (Magma.op a (Magma.op (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) (Magma.op a a)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25187
       have i₂ := eq783 (Magma.op z a) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) (Magma.op a a) a
       grind)
    | (have i₁ := eq25187
       have i₂ := eq783 (Magma.op z a) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a (Magma.op a a)
       grind)
    | exact superpose eq783 eq25187
    | exact resolve eq25187 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25187
  have eq25209 : (Magma.op (Magma.op a a) (Magma.op (Magma.op a (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) (Magma.op z a))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25201
       have i₂ := eq7536 a (Magma.op z a) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))) a a
       grind)
    | exact superpose eq7536 eq25201
    | exact resolve eq25201 eq7536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7536 eq25201
  have eq25217 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op z (Magma.op a (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))))))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25209
       have i₂ := eq783 (Magma.op a a) z (Magma.op a (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) a
       grind)
    | (have i₁ := eq25209
       have i₂ := eq783 (Magma.op a a) z a (Magma.op a (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a)))))
       grind)
    | exact superpose eq783 eq25209
    | exact resolve eq25209 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25209
  have eq25225 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op (Magma.op a (Magma.op y (Magma.op a a))) z) (Magma.op x a))) := by
    first
    | (have i₁ := eq25217
       have i₂ := eq20881 (Magma.op a (Magma.op y (Magma.op a a))) z (Magma.op x a) a a a
       grind)
    | exact superpose eq20881 eq25217
    | exact resolve eq25217 eq20881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20881 eq25217
  have eq25231 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op (Magma.op a (Magma.op y (Magma.op a a))) z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25225
       have i₂ := eq783 (Magma.op a a) x (Magma.op (Magma.op a (Magma.op y (Magma.op a a))) z) a
       grind)
    | (have i₁ := eq25225
       have i₂ := eq783 (Magma.op a a) x a (Magma.op (Magma.op a (Magma.op y (Magma.op a a))) z)
       grind)
    | exact superpose eq783 eq25225
    | exact resolve eq25225 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25225
  have eq25235 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op x (Magma.op (Magma.op a (Magma.op a (Magma.op a y))) z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25231
       have i₂ := eq783 a a y a
       grind)
    | (have i₁ := eq25231
       have i₂ := eq783 a a a y
       grind)
    | exact superpose eq783 eq25231
    | exact resolve eq25231 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25231
  have eq25239 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op a y) (Magma.op z a)) x)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25235
       have i₂ := eq13781 (Magma.op a y) z a x a
       grind)
    | (have i₁ := eq25235
       have i₂ := eq13781 a a (Magma.op a y) z x
       grind)
    | exact superpose eq13781 eq25235
    | exact resolve eq25235 eq13781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13781 eq25235
  have eq25243 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op a x) (Magma.op z a)) y)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25239
       have i₂ := eq24051 a (Magma.op z a) a y a x
       grind)
    | (have i₁ := eq25239
       have i₂ := eq24051 a (Magma.op z a) a x a y
       grind)
    | exact superpose eq24051 eq25239
    | exact resolve eq25239 eq24051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24051 eq25239
  have eq25247 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op z (Magma.op a x))) y)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25243
       have i₂ := eq13101 y a a (Magma.op a x) z
       grind)
    | (have i₁ := eq25243
       have i₂ := eq13101 y (Magma.op a x) a a z
       grind)
    | exact superpose eq13101 eq25243
    | exact resolve eq25243 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101 eq25243
  have eq25251 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op y (Magma.op a x))) z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25247
       have i₂ := eq14196 z a (Magma.op a x) y a
       grind)
    | (have i₁ := eq25247
       have i₂ := eq14196 y a (Magma.op a x) z a
       grind)
    | exact superpose eq14196 eq25247
    | exact resolve eq25247 eq14196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14196 eq25247
  have eq25255 : (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op x (Magma.op a y))) z)))) := by
    first
    | (have i₁ := eq25251
       have i₂ := eq783 a a y x
       grind)
    | (have i₁ := eq25251
       have i₂ := eq783 a a x y
       grind)
    | exact superpose eq783 eq25251
    | exact resolve eq25251 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq25251
  have eq25256 : False := by grind
  exact eq25256

theorem zero_add (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op (Magma.op a a) a) (Magma.op a (Magma.op x (Magma.op a a)))) = x := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : x ≠ (Magma.op (Magma.op (Magma.op a a) a) (Magma.op a (Magma.op x (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9 : x ≠ (Magma.op a (Magma.op a (Magma.op x (Magma.op a a)))) := by
    first
    | (have i₁ := eq4
       have i₂ := eq7 a a
       grind)
    | exact superpose eq7 eq4
    | exact resolve eq4 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq13 : False := by grind
  exact eq13

theorem add_zero (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op x a) (Magma.op a (Magma.op (Magma.op a a) (Magma.op a a)))) = x := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : x ≠ (Magma.op (Magma.op x a) (Magma.op a (Magma.op (Magma.op a a) (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 X1)) = (Magma.op X1 (Magma.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 (Magma.op X1 (Magma.op X2 X0)) X0 X2
       have i₂ := eq7 (Magma.op X2 X0) X1
       grind)
    | exact superpose eq7 eq3
    | exact resolve eq3 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : x ≠ (Magma.op (Magma.op x a) (Magma.op a (Magma.op a (Magma.op a (Magma.op a a))))) := by
    first
    | (have i₁ := eq4
       have i₂ := eq10 (Magma.op a a) a a
       grind)
    | (have i₁ := eq4
       have i₂ := eq10 a (Magma.op a a) a
       grind)
    | exact superpose eq10 eq4
    | exact resolve eq4 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10
  have eq158 : x ≠ (Magma.op (Magma.op x a) a) := by
    first
    | (have i₁ := eq153
       have i₂ := eq3 a a a
       grind)
    | exact superpose eq3 eq153
    | exact resolve eq153 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq169 : False := by grind
  exact eq169

theorem neg_add (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op a (Magma.op x (Magma.op a a)))) = (Magma.op a a) := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : (Magma.op a a) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op a (Magma.op x (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq6 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X0 (Magma.op X1 X2)) (Magma.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 X2 (Magma.op X0 (Magma.op X1 X2)) X1
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 X1)) = (Magma.op X1 (Magma.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 (Magma.op X1 (Magma.op X2 X0)) X0 X2
       have i₂ := eq7 (Magma.op X2 X0) X1
       grind)
    | exact superpose eq7 eq3
    | exact resolve eq3 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X3 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 X1 X2 (Magma.op X3 (Magma.op X0 (Magma.op X3 X2)))
       have i₂ := eq3 X0 X2 X3
       grind)
    | exact superpose eq3 eq6
    | exact resolve eq6 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op (Magma.op X1 (Magma.op X0 (Magma.op X1 X2))) (Magma.op X2 X3)) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (Magma.op X1 (Magma.op X0 (Magma.op X1 X2))) X2 X3
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq6
    | exact resolve eq6 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X1 (Magma.op X0 X1) X2
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq6
    | exact resolve eq6 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) (Magma.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X3 (Magma.op X1 X2) (Magma.op X2 (Magma.op X1 X0))
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq3
    | exact resolve eq3 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op X0 (Magma.op X3 (Magma.op X2 (Magma.op X1 X0))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X2 X3
       have i₂ := eq10 (Magma.op X2 (Magma.op X1 X0)) X0 X3
       grind)
    | (have i₁ := eq21 X0 X1 X2 X3
       have i₂ := eq10 X0 (Magma.op X2 (Magma.op X1 X0)) X3
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq25 : ∀ X0 X1 X2 X3 : G, (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) = (Magma.op X3 (Magma.op X0 (Magma.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3 X0 X1
       have i₂ := eq10 (Magma.op X3 X2) X3 X0
       grind)
    | (have i₁ := eq12 X2 X3 X0 X1
       have i₂ := eq10 X3 (Magma.op X3 X2) X0
       grind)
    | exact superpose eq10 eq12
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12
  have eq118 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X1 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 X0) X3 X2
       have i₂ := eq10 X2 X0 X1
       grind)
    | (have i₁ := eq10 (Magma.op X1 X0) X3 X2
       have i₂ := eq10 X0 X2 X1
       grind)
    | exact superpose eq10 eq10
    | exact resolve eq10 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (Magma.op X2 X0) = (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2 (Magma.op X0 X1)
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq10
    | exact resolve eq10 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq311 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op X0 (Magma.op X1 (Magma.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 X2 X3 (Magma.op X1 X0)
       have i₂ := eq10 (Magma.op X2 X3) X0 X1
       grind)
    | (have i₁ := eq119 X2 X3 (Magma.op X1 X0)
       have i₂ := eq10 X0 (Magma.op X2 X3) X1
       grind)
    | exact superpose eq10 eq119
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 (Magma.op X3 X2)) X0) = (Magma.op (Magma.op X2 (Magma.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 X1 (Magma.op (Magma.op X2 (Magma.op X0 X1)) X3)
       have i₂ := eq119 X2 (Magma.op X0 X1) X3
       grind)
    | exact superpose eq119 eq18
    | exact resolve eq18 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq413 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X1 (Magma.op (Magma.op (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) (Magma.op X3 X0)) (Magma.op X4 X0))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3 X4 X1 (Magma.op (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) (Magma.op X3 X0))
       have i₂ := eq17 X1 X2 X3 X0
       grind)
    | exact superpose eq17 eq3
    | exact resolve eq3 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq447 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X1 (Magma.op X0 (Magma.op X4 (Magma.op (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) (Magma.op X3 X0))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq413 X0 X1 X2 X3 X4
       have i₂ := eq10 (Magma.op (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) (Magma.op X3 X0)) X0 X4
       grind)
    | (have i₁ := eq413 X0 X1 X2 X3 X4
       have i₂ := eq10 X0 (Magma.op (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) (Magma.op X3 X0)) X4
       grind)
    | exact superpose eq10 eq413
    | exact resolve eq413 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq491 : ∀ X1 X2 X3 X4 : G, (Magma.op X1 (Magma.op (Magma.op (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) X4) X3)) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq447 x X1 X2 X3 X4
       have i₂ := eq311 X4 (Magma.op X2 (Magma.op X1 (Magma.op X2 X3))) X3 x
       grind)
    | exact superpose eq311 eq447
    | exact resolve eq447 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq783 : ∀ X0 X1 X2 X3 : G, (Magma.op X0 (Magma.op X2 (Magma.op X1 X3))) = (Magma.op X0 (Magma.op X3 (Magma.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (Magma.op X1 X3) X2 (Magma.op X0 (Magma.op X3 (Magma.op X1 X2)))
       have i₂ := eq22 X2 X1 X3 X0
       grind)
    | exact superpose eq22 eq6
    | exact resolve eq6 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6 eq22
  have eq1072 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X4 X3) X1)) = (Magma.op (Magma.op X3 (Magma.op X0 (Magma.op X1 (Magma.op X0 X2)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 X4 X3 (Magma.op X2 (Magma.op (Magma.op X4 X3) X1))
       have i₂ := eq25 X1 (Magma.op X4 X3) X2 X0
       grind)
    | (have i₁ := eq18 X4 X3 (Magma.op X2 (Magma.op (Magma.op X4 X3) X1))
       have i₂ := eq25 X2 X0 X1 (Magma.op X4 X3)
       grind)
    | exact superpose eq25 eq18
    | exact resolve eq18 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1074 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op X0 (Magma.op a (Magma.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq4
       have i₂ := eq25 a a x X0
       grind)
    | (have i₁ := eq4
       have i₂ := eq25 x X0 a a
       grind)
    | exact superpose eq25 eq4
    | exact resolve eq4 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1075 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op (Magma.op (Magma.op x (Magma.op a (Magma.op (Magma.op a a) (Magma.op a a)))) (Magma.op (Magma.op a a) (Magma.op a a))) (Magma.op X0 (Magma.op a (Magma.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq1074 X0
       have i₂ := eq340 a (Magma.op (Magma.op a a) (Magma.op a a)) x (Magma.op (Magma.op a a) (Magma.op a a))
       grind)
    | (have i₁ := eq1074 X0
       have i₂ := eq340 (Magma.op (Magma.op a a) (Magma.op a a)) x (Magma.op (Magma.op a a) (Magma.op a a)) a
       grind)
    | exact superpose eq340 eq1074
    | exact resolve eq1074 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq1074
  have eq1171 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op (Magma.op (Magma.op a (Magma.op a a)) (Magma.op a (Magma.op x (Magma.op a (Magma.op (Magma.op a a) (Magma.op a a)))))) (Magma.op X0 (Magma.op a (Magma.op X0 x)))) := by
    intro X0
    first
    | (have i₁ := eq1075 X0
       have i₂ := eq118 (Magma.op a a) a a (Magma.op x (Magma.op a (Magma.op (Magma.op a a) (Magma.op a a))))
       grind)
    | exact superpose eq118 eq1075
    | exact resolve eq1075 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq1075
  have eq1225 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a))) x)) := by
    intro X0
    first
    | (have i₁ := eq1171 X0
       have i₂ := eq1072 a x (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a (Magma.op a a)) (Magma.op X0 (Magma.op a (Magma.op X0 x)))
       grind)
    | exact superpose eq1072 eq1171
    | exact resolve eq1171 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq1171
  have eq1255 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op x (Magma.op (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a))) (Magma.op (Magma.op a a) (Magma.op a a)))) := by
    intro X0
    first
    | (have i₁ := eq1225 X0
       have i₂ := eq10 (Magma.op (Magma.op a a) (Magma.op a a)) x (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a)))
       grind)
    | (have i₁ := eq1225 X0
       have i₂ := eq10 x (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a)))
       grind)
    | exact superpose eq10 eq1225
    | exact resolve eq1225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1269 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op x (Magma.op (Magma.op a a) (Magma.op (Magma.op a a) (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a)))))) := by
    intro X0
    first
    | (have i₁ := eq1255 X0
       have i₂ := eq783 x (Magma.op a a) (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a))) (Magma.op a a)
       grind)
    | (have i₁ := eq1255 X0
       have i₂ := eq783 x (Magma.op a a) (Magma.op a a) (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a (Magma.op a a)))
       grind)
    | exact superpose eq783 eq1255
    | exact resolve eq1255 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq1255
  have eq1277 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op x (Magma.op (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a a)) a)) := by
    intro X0
    first
    | (have i₁ := eq1269 X0
       have i₂ := eq311 (Magma.op a a) (Magma.op X0 (Magma.op a (Magma.op X0 x))) a (Magma.op a a)
       grind)
    | exact superpose eq311 eq1269
    | exact resolve eq1269 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq1269
  have eq1283 : ∀ X0 : G, (Magma.op a a) ≠ (Magma.op a (Magma.op (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a a)) x)) := by
    intro X0
    first
    | (have i₁ := eq1277 X0
       have i₂ := eq10 x a (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a a))
       grind)
    | (have i₁ := eq1277 X0
       have i₂ := eq10 a x (Magma.op (Magma.op X0 (Magma.op a (Magma.op X0 x))) (Magma.op a a))
       grind)
    | exact superpose eq10 eq1277
    | exact resolve eq1277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10 eq1277
  have eq1287 : False := by grind
  exact eq1287

theorem j_add (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) = (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op a a)))) := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq5 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 (Magma.op X0 (Magma.op X1 X2))) (Magma.op X2 (Magma.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X3 (Magma.op X1 (Magma.op X0 (Magma.op X1 X2))) X2
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X0 (Magma.op X1 X2)) (Magma.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 X2 (Magma.op X0 (Magma.op X1 X2)) X1
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1))) X1
       have i₂ := eq3 X0 X1 X2
       grind)
    | exact superpose eq3 eq7
    | exact resolve eq7 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 X1)) = (Magma.op X1 (Magma.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 (Magma.op X1 (Magma.op X2 X0)) X0 X2
       have i₂ := eq7 (Magma.op X2 X0) X1
       grind)
    | exact superpose eq7 eq3
    | exact resolve eq3 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X3 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 X1 X2 (Magma.op X3 (Magma.op X0 (Magma.op X3 X2)))
       have i₂ := eq3 X0 X2 X3
       grind)
    | exact superpose eq3 eq6
    | exact resolve eq6 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X1 (Magma.op X0 X1) X2
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq6
    | exact resolve eq6 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) (Magma.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X3 (Magma.op X1 X2) (Magma.op X2 (Magma.op X1 X0))
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq3
    | exact resolve eq3 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op X0 (Magma.op X3 (Magma.op X2 (Magma.op X1 X0))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X2 X3
       have i₂ := eq10 (Magma.op X2 (Magma.op X1 X0)) X0 X3
       grind)
    | (have i₁ := eq21 X0 X1 X2 X3
       have i₂ := eq10 X0 (Magma.op X2 (Magma.op X1 X0)) X3
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq25 : ∀ X0 X1 X2 X3 : G, (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) = (Magma.op X3 (Magma.op X0 (Magma.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3 X0 X1
       have i₂ := eq10 (Magma.op X3 X2) X3 X0
       grind)
    | (have i₁ := eq12 X2 X3 X0 X1
       have i₂ := eq10 X3 (Magma.op X3 X2) X0
       grind)
    | exact superpose eq10 eq12
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12
  have eq116 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 X0) = (Magma.op (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) (Magma.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) X3 X2
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq10
    | exact resolve eq10 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (Magma.op X2 X0) = (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 X2 (Magma.op X0 X1)
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq10
    | exact resolve eq10 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq120 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 X0) = (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 (Magma.op X1 X2) X3 (Magma.op X2 (Magma.op X1 X0))
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq10
    | exact resolve eq10 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 X1)) = (Magma.op (Magma.op (Magma.op X1 (Magma.op X2 X3)) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 (Magma.op X1 (Magma.op X2 X3)) (Magma.op X3 (Magma.op X0 X1))
       have i₂ := eq5 X1 X2 X3 X0
       grind)
    | exact superpose eq5 eq18
    | exact resolve eq18 eq5
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5
  have eq228 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op (Magma.op X2 X1) (Magma.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X2 X1 (Magma.op X3 (Magma.op (Magma.op X2 X1) (Magma.op X3 X0)))
       have i₂ := eq8 (Magma.op X2 X1) X0 X3
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8
  have eq297 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op X0 (Magma.op X1 (Magma.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq119 X2 X3 (Magma.op X1 X0)
       have i₂ := eq10 (Magma.op X2 X3) X0 X1
       grind)
    | (have i₁ := eq119 X2 X3 (Magma.op X1 X0)
       have i₂ := eq10 X0 (Magma.op X2 X3) X1
       grind)
    | exact superpose eq10 eq119
    | exact resolve eq119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10
  have eq326 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 (Magma.op X3 X2)) X0) = (Magma.op (Magma.op X2 (Magma.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18 X0 X1 (Magma.op (Magma.op X2 (Magma.op X0 X1)) X3)
       have i₂ := eq119 X2 (Magma.op X0 X1) X3
       grind)
    | exact superpose eq119 eq18
    | exact resolve eq18 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq745 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X3) (Magma.op X2 X0)) = (Magma.op (Magma.op X1 X2) (Magma.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 X1 X3 (Magma.op (Magma.op X1 X2) (Magma.op X3 X0))
       have i₂ := eq6 (Magma.op X1 X2) X3 X0
       grind)
    | exact superpose eq6 eq22
    | exact resolve eq22 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6
  have eq943 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X3 (Magma.op (Magma.op X2 (Magma.op X4 X1)) (Magma.op X3 X5))) = (Magma.op X4 (Magma.op X5 (Magma.op X0 (Magma.op X1 (Magma.op X0 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 X5 X3 (Magma.op X2 (Magma.op X4 X1)) X4
       have i₂ := eq25 X1 X4 X2 X0
       grind)
    | (have i₁ := eq25 X5 X3 (Magma.op X2 (Magma.op X4 X1)) X4
       have i₂ := eq25 X2 X0 X1 X4
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1128 : ∀ X0 X1 X2 X4 X5 : G, (Magma.op X4 (Magma.op X5 (Magma.op X0 (Magma.op X1 (Magma.op X0 X2))))) = (Magma.op (Magma.op (Magma.op X4 X1) X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq943 X0 X1 X2 x X4 X5
       have i₂ := eq228 X5 (Magma.op X4 X1) X2 x
       grind)
    | exact superpose eq228 eq943
    | exact resolve eq943 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq943
  have eq7456 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X1 X3) X0)) = (Magma.op (Magma.op X3 (Magma.op X4 (Magma.op X0 X1))) (Magma.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 (Magma.op (Magma.op X1 X3) X0) X3 X4 X2
       have i₂ := eq119 X1 X3 X0
       grind)
    | exact superpose eq119 eq116
    | exact resolve eq116 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq7488 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X1 (Magma.op X0 (Magma.op X2 (Magma.op X3 X4)))) = (Magma.op (Magma.op X4 X0) (Magma.op (Magma.op X3 X2) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq116 (Magma.op X0 (Magma.op X2 (Magma.op X3 X4))) X4 (Magma.op X3 X2) X1
       have i₂ := eq22 X4 X3 X2 X0
       grind)
    | exact superpose eq22 eq116
    | exact resolve eq116 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq116
  have eq7811 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X1 X3) X0)) = (Magma.op (Magma.op X3 X4) (Magma.op (Magma.op X4 (Magma.op X0 X1)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq7456 X0 X1 X2 X3 X4
       have i₂ := eq745 X2 X3 X4 (Magma.op X4 (Magma.op X0 X1))
       grind)
    | (have i₁ := eq7456 X0 X1 X2 X3 X4
       have i₂ := eq745 X2 X3 (Magma.op X4 (Magma.op X0 X1)) X4
       grind)
    | exact superpose eq745 eq7456
    | exact resolve eq7456 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq7456
  have eq12676 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X2 (Magma.op (Magma.op X3 (Magma.op X4 X1)) X0)) = (Magma.op (Magma.op (Magma.op X4 X3) X5) (Magma.op (Magma.op X5 (Magma.op X0 X1)) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq120 (Magma.op (Magma.op X3 (Magma.op X4 X1)) X0) (Magma.op X4 X3) X5 X2
       have i₂ := eq120 X1 X4 X3 X0
       grind)
    | exact superpose eq120 eq120
    | exact resolve eq120 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq13051 : ∀ X0 X1 X2 X3 X4 : G, (Magma.op X2 (Magma.op (Magma.op X3 (Magma.op X4 X1)) X0)) = (Magma.op X2 (Magma.op (Magma.op X1 (Magma.op X4 X3)) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12676 X0 X1 X2 X3 X4 x
       have i₂ := eq7811 X0 X1 X2 (Magma.op X4 X3) x
       grind)
    | exact superpose eq7811 eq12676
    | exact resolve eq12676 eq7811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7811 eq12676
  have eq13660 : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) ≠ (Magma.op (Magma.op a (Magma.op x (Magma.op a a))) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op a a)))) := by
    first
    | (have i₁ := eq4
       have i₂ := eq226 x (Magma.op a a) a a
       grind)
    | exact superpose eq226 eq4
    | exact resolve eq4 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq13865 : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y)) (Magma.op a (Magma.op x (Magma.op a a))))) := by
    first
    | (have i₁ := eq13660
       have i₂ := eq7488 a (Magma.op a (Magma.op x (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a a
       grind)
    | exact superpose eq7488 eq13660
    | exact resolve eq13660 eq7488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7488 eq13660
  have eq14032 : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) ≠ (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y))) x) := by
    first
    | (have i₁ := eq13865
       have i₂ := eq297 (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y)) a x (Magma.op a a)
       grind)
    | exact superpose eq297 eq13865
    | exact resolve eq13865 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq13865
  have eq14144 : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op x a) (Magma.op a (Magma.op y (Magma.op a a))))) ≠ (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op a (Magma.op a a))) y))) x) := by
    first
    | (have i₁ := eq14032
       have i₂ := eq13051 y a a (Magma.op a a) a
       grind)
    | (have i₁ := eq14032
       have i₂ := eq13051 y (Magma.op a a) a a a
       grind)
    | exact superpose eq13051 eq14032
    | exact resolve eq14032 eq13051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14032
  have eq14216 : (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op x a)) a) ≠ (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op a (Magma.op a a))) y))) x) := by
    first
    | (have i₁ := eq14144
       have i₂ := eq1128 a y a (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op x a)
       grind)
    | exact superpose eq1128 eq14144
    | exact resolve eq14144 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq14144
  have eq14276 : (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y))) x) ≠ (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op a (Magma.op a a))) y))) x) := by
    first
    | (have i₁ := eq14216
       have i₂ := eq326 a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a x
       grind)
    | (have i₁ := eq14216
       have i₂ := eq326 x a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a
       grind)
    | exact superpose eq326 eq14216
    | exact resolve eq14216 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq14216
  have eq14315 : (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op a (Magma.op a a))) y))) x) ≠ (Magma.op (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op a (Magma.op a a))) y))) x) := by
    first
    | (have i₁ := eq14276
       have i₂ := eq13051 y a a (Magma.op a a) a
       grind)
    | (have i₁ := eq14276
       have i₂ := eq13051 y (Magma.op a a) a a a
       grind)
    | exact superpose eq13051 eq14276
    | exact resolve eq14276 eq13051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13051 eq14276
  have eq14316 : False := by grind
  exact eq14316

theorem j_zero (h : Equation546 G) (a x y z : G) : (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)) = (Magma.op a a) := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : (Magma.op a a) ≠ (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)) := by grind
  clear hlaw hn
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9 : (Magma.op a a) ≠ (Magma.op a a) := by
    first
    | (have i₁ := eq4
       have i₂ := eq7 (Magma.op a a) (Magma.op a a)
       grind)
    | exact superpose eq7 eq4
    | (have r₁ := eq4
       have r₂ := eq7 (Magma.op a a) (Magma.op a a)
       grind)
    | exact resolve eq4 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq12 : False := by grind
  exact eq12

theorem affine (h : Equation546 G) (a x y z : G) : (Magma.op x y) = (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))) (Magma.op a a)))) := by
  by_contra hn
  have hlaw (x y z : G) := (h x y z).symm
  have eq3 : ∀ X0 X1 X2 : G, (Magma.op X1 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq4 : (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))) (Magma.op a a)))) := by grind
  clear hlaw hn
  have eq6 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X0 (Magma.op X1 X2)) (Magma.op X1 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 X2 (Magma.op X0 (Magma.op X1 X2)) X1
       have i₂ := eq3 X0 X2 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7 : ∀ X0 X1 : G, (Magma.op (Magma.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3 X1 (Magma.op X1 X0) X0
       have i₂ := eq3 X0 X0 X1
       grind)
    | exact superpose eq3 eq3
    | exact resolve eq3 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7 (Magma.op X2 (Magma.op X0 (Magma.op X2 X1))) X1
       have i₂ := eq3 X0 X1 X2
       grind)
    | exact superpose eq3 eq7
    | exact resolve eq7 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11 : ∀ X0 X1 X2 : G, (Magma.op X0 (Magma.op X2 X1)) = (Magma.op X1 (Magma.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3 (Magma.op X1 (Magma.op X2 X0)) X0 X2
       have i₂ := eq7 (Magma.op X2 X0) X1
       grind)
    | exact superpose eq7 eq3
    | exact resolve eq3 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X3 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 X1 X2 (Magma.op X3 (Magma.op X0 (Magma.op X3 X2)))
       have i₂ := eq3 X0 X2 X3
       grind)
    | exact superpose eq3 eq6
    | exact resolve eq6 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (Magma.op (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6 X1 (Magma.op X0 X1) X2
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq6
    | exact resolve eq6 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op (Magma.op X2 (Magma.op X1 X0)) (Magma.op X3 X0))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3 X3 (Magma.op X1 X2) (Magma.op X2 (Magma.op X1 X0))
       have i₂ := eq6 X2 X1 X0
       grind)
    | exact superpose eq6 eq3
    | exact resolve eq3 eq6
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X2) (Magma.op X0 (Magma.op X3 (Magma.op X2 (Magma.op X1 X0))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq29 X0 X1 X2 X3
       have i₂ := eq11 (Magma.op X2 (Magma.op X1 X0)) X0 X3
       grind)
    | (have i₁ := eq29 X0 X1 X2 X3
       have i₂ := eq11 X0 (Magma.op X2 (Magma.op X1 X0)) X3
       grind)
    | exact superpose eq11 eq29
    | exact resolve eq29 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq33 : ∀ X0 X1 X2 X3 : G, (Magma.op X1 (Magma.op X2 (Magma.op X1 X0))) = (Magma.op X3 (Magma.op X0 (Magma.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X2 X3 X0 X1
       have i₂ := eq11 (Magma.op X3 X2) X3 X0
       grind)
    | (have i₁ := eq20 X2 X3 X0 X1
       have i₂ := eq11 X3 (Magma.op X3 X2) X0
       grind)
    | exact superpose eq11 eq20
    | exact resolve eq20 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq126 : ∀ X0 X1 X2 X3 : G, (Magma.op X3 (Magma.op X0 (Magma.op X1 X2))) = (Magma.op (Magma.op X1 X0) (Magma.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (Magma.op X1 X0) X3 X2
       have i₂ := eq11 X2 X0 X1
       grind)
    | (have i₁ := eq11 (Magma.op X1 X0) X3 X2
       have i₂ := eq11 X0 X2 X1
       grind)
    | exact superpose eq11 eq11
    | exact resolve eq11 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 : G, (Magma.op X2 X0) = (Magma.op X1 (Magma.op (Magma.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X2 (Magma.op X0 X1)
       have i₂ := eq7 X1 X0
       grind)
    | exact superpose eq7 eq11
    | exact resolve eq11 eq7
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7
  have eq391 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op X0 (Magma.op X3 (Magma.op X2 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 X1 (Magma.op X3 (Magma.op X0 (Magma.op X3 (Magma.op X2 X1))))
       have i₂ := eq3 X0 (Magma.op X2 X1) X3
       grind)
    | exact superpose eq3 eq26
    | exact resolve eq26 eq3
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op (Magma.op X2 X1) (Magma.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 X1 (Magma.op X3 (Magma.op (Magma.op X2 X1) (Magma.op X3 X0)))
       have i₂ := eq8 (Magma.op X2 X1) X0 X3
       grind)
    | exact superpose eq8 eq26
    | exact resolve eq26 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8 eq26
  have eq461 : ∀ X0 X1 X2 X3 : G, (Magma.op (Magma.op X1 X0) X2) = (Magma.op X3 (Magma.op X0 (Magma.op X1 (Magma.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X2 X3 (Magma.op X1 X0)
       have i₂ := eq11 (Magma.op X2 X3) X0 X1
       grind)
    | (have i₁ := eq127 X2 X3 (Magma.op X1 X0)
       have i₂ := eq11 X0 (Magma.op X2 X3) X1
       grind)
    | exact superpose eq11 eq127
    | exact resolve eq127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11
  have eq933 : ∀ X0 X1 X2 X3 : G, (Magma.op X0 (Magma.op X2 (Magma.op X1 X3))) = (Magma.op X0 (Magma.op X3 (Magma.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6 (Magma.op X1 X3) X2 (Magma.op X0 (Magma.op X3 (Magma.op X1 X2)))
       have i₂ := eq30 X2 X1 X3 X0
       grind)
    | exact superpose eq30 eq6
    | exact resolve eq6 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6 eq30
  have eq1107 : ∀ X0 X1 X2 X3 X4 X5 : G, (Magma.op X3 (Magma.op (Magma.op X2 (Magma.op X4 X1)) (Magma.op X3 X5))) = (Magma.op X4 (Magma.op X5 (Magma.op X0 (Magma.op X1 (Magma.op X0 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq33 X5 X3 (Magma.op X2 (Magma.op X4 X1)) X4
       have i₂ := eq33 X1 X4 X2 X0
       grind)
    | (have i₁ := eq33 X5 X3 (Magma.op X2 (Magma.op X4 X1)) X4
       have i₂ := eq33 X2 X0 X1 X4
       grind)
    | exact superpose eq33 eq33
    | exact resolve eq33 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : ∀ X0 : G, (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op X0 (Magma.op a (Magma.op X0 (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))))))) := by
    intro X0
    first
    | (have i₁ := eq4
       have i₂ := eq33 a a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))) X0
       grind)
    | (have i₁ := eq4
       have i₂ := eq33 (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))) X0 a a
       grind)
    | exact superpose eq33 eq4
    | exact resolve eq4 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1227 : (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a))) := by
    first
    | (have i₁ := eq1226 x
       have i₂ := eq391 a (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) x
       grind)
    | exact superpose eq391 eq1226
    | exact resolve eq1226 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1296 : ∀ X0 X1 X2 X4 X5 : G, (Magma.op X4 (Magma.op X5 (Magma.op X0 (Magma.op X1 (Magma.op X0 X2))))) = (Magma.op (Magma.op (Magma.op X4 X1) X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq1107 X0 X1 X2 x X4 X5
       have i₂ := eq392 X5 (Magma.op X4 X1) X2 x
       grind)
    | exact superpose eq392 eq1107
    | exact resolve eq1107 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq1107
  have eq1325 : (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a)))) := by
    first
    | (have i₁ := eq1227
       have i₂ := eq933 (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a) a
       grind)
    | (have i₁ := eq1227
       have i₂ := eq933 (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a)
       grind)
    | exact superpose eq933 eq1227
    | exact resolve eq1227 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1381 : (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a))) := by
    first
    | (have i₁ := eq1325
       have i₂ := eq126 a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a)
       grind)
    | exact superpose eq126 eq1325
    | exact resolve eq1325 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1413 : (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a)))) := by
    first
    | (have i₁ := eq1381
       have i₂ := eq933 (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a) a
       grind)
    | (have i₁ := eq1381
       have i₂ := eq933 (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a)
       grind)
    | exact superpose eq933 eq1381
    | exact resolve eq1381 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1429 : (Magma.op x y) ≠ (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op a (Magma.op a (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)))))) := by
    first
    | (have i₁ := eq1413
       have i₂ := eq933 a (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a
       grind)
    | (have i₁ := eq1413
       have i₂ := eq933 a (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x))
       grind)
    | exact superpose eq933 eq1413
    | exact resolve eq1413 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1439 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x))) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a))) := by
    first
    | (have i₁ := eq1429
       have i₂ := eq126 a a (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x))) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a)
       grind)
    | exact superpose eq126 eq1429
    | exact resolve eq1429 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq1429
  have eq1447 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)))))) := by
    first
    | (have i₁ := eq1439
       have i₂ := eq933 (Magma.op a a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x))) a
       grind)
    | (have i₁ := eq1439
       have i₂ := eq933 (Magma.op a a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a (Magma.op (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)))
       grind)
    | exact superpose eq933 eq1439
    | exact resolve eq1439 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1453 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))))))) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq933 (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a))) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)
       grind)
    | (have i₁ := eq1447
       have i₂ := eq933 (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) (Magma.op a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)))
       grind)
    | exact superpose eq933 eq1447
    | exact resolve eq1447 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq1457 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) (Magma.op a a)))) := by
    first
    | (have i₁ := eq1453
       have i₂ := eq1296 (Magma.op (Magma.op a a) (Magma.op a a)) a (Magma.op a a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)
       grind)
    | exact superpose eq1296 eq1453
    | exact resolve eq1453 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq1461 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)))))) := by
    first
    | (have i₁ := eq1457
       have i₂ := eq933 a a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)) a
       grind)
    | (have i₁ := eq1457
       have i₂ := eq933 a a a (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x))
       grind)
    | exact superpose eq933 eq1457
    | exact resolve eq1457 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq1465 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a))) := by
    first
    | (have i₁ := eq1461
       have i₂ := eq391 a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a) a
       grind)
    | exact superpose eq391 eq1461
    | exact resolve eq1461 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq1461
  have eq1469 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a)))) := by
    first
    | (have i₁ := eq1465
       have i₂ := eq933 (Magma.op a a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a) a
       grind)
    | (have i₁ := eq1465
       have i₂ := eq933 (Magma.op a a) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a)
       grind)
    | exact superpose eq933 eq1465
    | exact resolve eq1465 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1473 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y))))) := by
    first
    | (have i₁ := eq1469
       have i₂ := eq933 a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y) a
       grind)
    | (have i₁ := eq1469
       have i₂ := eq933 a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) a (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) y)
       grind)
    | exact superpose eq933 eq1469
    | exact resolve eq1469 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1477 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op y (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)))))) := by
    first
    | (have i₁ := eq1473
       have i₂ := eq933 a (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x) y
       grind)
    | (have i₁ := eq1473
       have i₂ := eq933 a (Magma.op (Magma.op a a) (Magma.op a a)) y (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) x)
       grind)
    | exact superpose eq933 eq1473
    | exact resolve eq1473 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1481 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op y (Magma.op x (Magma.op (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op a a) (Magma.op a a)))))))) := by
    first
    | (have i₁ := eq1477
       have i₂ := eq933 y (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op (Magma.op a a) (Magma.op a a)) x
       grind)
    | (have i₁ := eq1477
       have i₂ := eq933 y (Magma.op (Magma.op a a) (Magma.op a a)) x (Magma.op (Magma.op a a) (Magma.op a a))
       grind)
    | exact superpose eq933 eq1477
    | exact resolve eq1477 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1485 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op y (Magma.op x (Magma.op (Magma.op a a) (Magma.op (Magma.op a a) (Magma.op (Magma.op a a) (Magma.op a a))))))))) := by
    first
    | (have i₁ := eq1481
       have i₂ := eq933 x (Magma.op a a) (Magma.op (Magma.op a a) (Magma.op a a)) (Magma.op a a)
       grind)
    | (have i₁ := eq1481
       have i₂ := eq933 x (Magma.op a a) (Magma.op a a) (Magma.op (Magma.op a a) (Magma.op a a))
       grind)
    | exact superpose eq933 eq1481
    | exact resolve eq1481 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq1481
  have eq1489 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op a (Magma.op a (Magma.op (Magma.op (Magma.op y (Magma.op a a)) x) (Magma.op a a))))) := by
    first
    | (have i₁ := eq1485
       have i₂ := eq1296 (Magma.op a a) (Magma.op a a) (Magma.op a a) y x
       grind)
    | exact superpose eq1296 eq1485
    | exact resolve eq1485 eq1296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296 eq1485
  have eq1493 : (Magma.op x y) ≠ (Magma.op (Magma.op a a) (Magma.op (Magma.op y (Magma.op a a)) x)) := by
    first
    | (have i₁ := eq1489
       have i₂ := eq461 a a (Magma.op (Magma.op y (Magma.op a a)) x) (Magma.op a a)
       grind)
    | exact superpose eq461 eq1489
    | exact resolve eq1489 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq1489
  have eq1497 : False := by grind
  exact eq1497

end Spectrum.GaussianRepresentation
