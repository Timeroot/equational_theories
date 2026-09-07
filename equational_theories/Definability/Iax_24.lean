import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_x_pyx_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X1)
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X1 X0
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq24 X0 X0
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ X0) (σ X1)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq47
    | exact resolve eq47 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq47 X1 (τ X0)
       grind)
    | exact superpose eq47 eq16
    | (have j1 := eq47 X1 (τ X0)
       grind)
    | exact resolve eq16 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X1)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq21
    | (have j1 := eq45 X1 X0
       grind)
    | exact resolve eq21 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq961 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1217 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1217
    | (have j0 := eq1217 X0 X1
       grind)
    | exact resolve eq1217 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1665 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq95 y x
       grind)
    | exact superpose eq95 eq14
    | (have j1 := eq95 y x
       grind)
    | exact resolve eq14 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq4719 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq540 (τ X0) (τ X1)
       have i₂ := eq145 X0 X1
       grind)
    | exact superpose eq145 eq540
    | exact resolve eq540 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq4773 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4719 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4719
    | (have j0 := eq4719 X0 X1
       grind)
    | exact resolve eq4719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4782 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4773 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4773
    | (have j0 := eq4773 X0 X1
       grind)
    | exact resolve eq4773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4773
  have eq4786 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4782 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4782
    | (have j0 := eq4782 X0 X1
       grind)
    | exact resolve eq4782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782
  have eq4787 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4786 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4786
    | (have j0 := eq4786 X0 X1
       grind)
    | exact resolve eq4786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4786
  have eq4788 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4787 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4787
    | (have j0 := eq4787 X0 X1
       grind)
    | exact resolve eq4787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq4808 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4788 (M.op X0 X0) X1
       have i₂ := eq64 (M.op X0 X0) X0
       grind)
    | exact superpose eq64 eq4788
    | (have j0 := eq4788 (M.op X0 X0) X1
       grind)
    | exact resolve eq4788 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq4848 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4808 X0 X1
       have j1 := eq47 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq4808 X0 X1
       have r₂ := eq47 (M.op X0 X0) X1
       grind)
    | exact resolve eq4808 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4808
  have eq4865 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4848 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq4848
    | exact resolve eq4848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4848
  have eq4887 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq499 X0 (M.op X0 X0)
       have i₂ := eq961 X0
       grind)
    | exact superpose eq961 eq499
    | (have j0 := eq499 X0 (M.op X0 X0)
       grind)
    | exact resolve eq499 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4913 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq499 (τ X0) (τ X1)
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq499
    | (have j0 := eq499 (τ X0) (τ X1)
       grind)
    | exact resolve eq499 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4968 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4913 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4913
    | (have j0 := eq4913 X0 X1
       grind)
    | exact resolve eq4913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4913
  have eq4977 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4968 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4968
    | (have j0 := eq4968 X0 X1
       grind)
    | exact resolve eq4968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968
  have eq4978 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4977 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4977
    | (have j0 := eq4977 X0 X1
       grind)
    | exact resolve eq4977 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4977
  have eq4979 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4978 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4978
    | (have j0 := eq4978 X0 X1
       grind)
    | exact resolve eq4978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978
  have eq5033 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq4865 X1 (τ X0)
       grind)
    | exact superpose eq4865 eq16
    | exact resolve eq16 eq4865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq4865
  have eq5036 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5033 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5033
    | exact resolve eq5033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5033
  have eq5053 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq539 (M.op X0 X0) X0
       have i₂ := eq961 X0
       grind)
    | exact superpose eq961 eq539
    | (have j0 := eq539 (M.op X0 X0) X0
       grind)
    | exact resolve eq539 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5077 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq539 (τ X1) (τ X0)
       have i₂ := eq145 X1 X0
       grind)
    | exact superpose eq145 eq539
    | (have j0 := eq539 (τ X1) (τ X0)
       grind)
    | exact resolve eq539 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq539
  have eq5127 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5077 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5077
    | (have j0 := eq5077 X0 X1
       grind)
    | exact resolve eq5077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5077
  have eq5133 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5053 X0
       have j1 := eq4887 X0
       grind)
    | (have r₁ := eq5053 X0
       have r₂ := eq4887 X0
       grind)
    | exact resolve eq5053 eq4887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4887 eq5053
  have eq5139 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op (σ (τ X0)) (σ (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5127 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5127
    | (have j0 := eq5127 X0 X1
       grind)
    | exact resolve eq5127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5127
  have eq5142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5139 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5139
    | (have j0 := eq5139 X0 X1
       grind)
    | exact resolve eq5139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139
  have eq5144 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5142 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5142
    | (have j0 := eq5142 X0 X1
       grind)
    | exact resolve eq5142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142
  have eq5196 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47 (σ (M.op X1 X1)) X0
       have i₂ := eq5036 X0 X1
       grind)
    | exact superpose eq5036 eq47
    | exact resolve eq47 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq5203 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ≠ X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4788 (σ (M.op X1 X1)) X0
       have i₂ := eq5036 X0 X1
       grind)
    | exact superpose eq5036 eq4788
    | (have r₁ := eq4788 (σ (M.op X1 X1)) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))
       have r₂ := eq5036 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       grind)
    | exact resolve eq4788 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788
  have eq5204 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq961 (σ (M.op X0 X0))
       have i₂ := eq5036 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq5036 eq961
    | exact resolve eq961 eq5036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq5221 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5203 X0 X1
       have i₂ := eq5204 X1
       grind)
    | exact superpose eq5204 eq5203
    | (have j0 := eq5203 X0 X1
       grind)
    | (have r₁ := eq5203 (σ (M.op X0 X0)) X0
       have r₂ := eq5204 X0
       grind)
    | exact resolve eq5203 eq5204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203 eq5204
  have eq5242 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5221 X0 X1
       have j1 := eq5196 X0 X1
       grind)
    | (have r₁ := eq5221 (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) X1
       have r₂ := eq5196 (σ (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq5221 X0 X1
       have r₂ := eq5196 X0 X1
       grind)
    | (have r₁ := eq5221 (σ (M.op X1 X1)) X1
       have r₂ := eq5196 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq5221 eq5196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5196 eq5221
  have eq5669 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ (M.op X1 X1)) X0
       have i₂ := eq5242 X0 X1
       grind)
    | exact superpose eq5242 eq21
    | exact resolve eq21 eq5242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq5242
  have eq15332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5669 (σ X0) X0
       have i₂ := eq5133 X0
       grind)
    | exact superpose eq5133 eq5669
    | exact resolve eq5669 eq5133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5133 eq5669
  have eq35620 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq1665
       have i₂ := eq1270 x y
       grind)
    | exact superpose eq1270 eq1665
    | (have j1 := eq1270 x y
       grind)
    | (have r₁ := eq1665
       have r₂ := eq1270 x y
       grind)
    | exact resolve eq1665 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270 eq1665
  have eq35621 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
  clear eq35620
  have eq35627 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq35621
       grind)
    | exact superpose eq35621 eq9
    | exact resolve eq9 eq35621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35621
  have eq35728 : y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq35627
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq35627
    | exact resolve eq35627 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35627
  have eq35733 : y = (k y x) := by
    first
    | (have j1 := eq100 y x
       grind)
    | (have r₁ := eq35728
       have r₂ := eq100 y x
       grind)
    | exact resolve eq35728 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq35728
  have eq36813 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq499 y x
       have i₂ := eq35733
       grind)
    | exact superpose eq35733 eq499
    | (have j0 := eq499 y x
       grind)
    | exact resolve eq499 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq36816 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4979 y x
       have i₂ := eq35733
       grind)
    | exact superpose eq35733 eq4979
    | (have j0 := eq4979 y x
       grind)
    | exact resolve eq4979 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4979
  have eq36817 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5144 y x
       have i₂ := eq35733
       grind)
    | exact superpose eq35733 eq5144
    | (have j0 := eq5144 y x
       grind)
    | exact resolve eq5144 eq35733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5144
  have eq36818 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq36816
       have r₂ := eq36817
       grind)
    | exact resolve eq36816 eq36817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36816 eq36817
  have eq36819 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36813
       have i₂ := eq15332 y
       grind)
    | exact superpose eq15332 eq36813
    | exact resolve eq36813 eq15332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36813
  have eq36820 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq36819
       have i₂ := eq36818
       grind)
    | exact superpose eq36818 eq36819
    | exact resolve eq36819 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36819
  have eq36821 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36820
       have i₂ := eq15332 y
       grind)
    | exact superpose eq15332 eq36820
    | exact resolve eq36820 eq15332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36820
  have eq36822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36821
       have i₂ := eq36818
       grind)
    | exact superpose eq36818 eq36821
    | exact resolve eq36821 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36821
  have eq36823 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq36822
       have r₂ := eq14
       grind)
    | exact resolve eq36822 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36822
  have eq37067 : ∀ X0 : G, (k (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5036 X0 y
       have i₂ := eq36818
       grind)
    | exact superpose eq36818 eq5036
    | exact resolve eq5036 eq36818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036 eq36818
  have eq37180 : ∀ X0 : G, (k (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37067 X0
       have i₂ := eq36823
       grind)
    | exact superpose eq36823 eq37067
    | exact resolve eq37067 eq36823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36823 eq37067
  have eq37591 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 (σ y) X0
       have i₂ := eq37180 (σ X0)
       grind)
    | exact superpose eq37180 eq20
    | exact resolve eq20 eq37180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq37180
  have eq37625 : ∀ X0 : G, (τ (σ X0)) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq37591 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq37591
    | exact resolve eq37591 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37591
  have eq37651 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq37625 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37625
    | exact resolve eq37625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37625
  have eq37898 : x = y := by
    first
    | (have i₁ := eq35733
       have i₂ := eq37651 x
       grind)
    | exact superpose eq37651 eq35733
    | exact resolve eq35733 eq37651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35733 eq37651
  have eq38622 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq37898
       grind)
    | exact superpose eq37898 eq14
    | exact resolve eq14 eq37898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37898
  have eq38631 : False := by grind
  exact eq38631

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pyy_pyx_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X2
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X1
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq56 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 X1
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq102 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq218 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq42 X2 X0
       grind)
    | exact superpose eq42 eq22
    | (have j1 := eq42 X2 X0
       grind)
    | exact resolve eq22 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq257 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq20
    | exact resolve eq20 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) ≠ (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq102
    | exact resolve eq102 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq575 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq579 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq612 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq575 (σ X0)
       grind)
    | exact superpose eq575 eq13
    | exact resolve eq13 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq612
    | exact resolve eq612 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq755 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) (σ X1))) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X1)
       have i₂ := eq579 X0 (σ X1)
       grind)
    | exact superpose eq579 eq61
    | exact resolve eq61 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq579
  have eq761 : ∀ X0 X1 : G, (k X1 X1) = (τ (k (M.op X0 X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq755
    | exact resolve eq755 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq781 : ∀ X0 X1 : G, (k X1 X1) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq761 X0 X1
       have i₂ := eq20 (M.op X0 X0) X1
       grind)
    | exact superpose eq20 eq761
    | exact resolve eq761 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq761
  have eq1000 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1076 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1000 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1000
    | (have j0 := eq1000 X0 X1
       grind)
    | exact resolve eq1000 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1319 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq619 X0
       grind)
    | exact superpose eq619 eq22
    | exact resolve eq22 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq1893 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq218 y X0 x
       grind)
    | exact superpose eq218 eq14
    | (have j1 := eq218 y X0 x
       grind)
    | exact resolve eq14 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq34609 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1893 X0
       have i₂ := eq1076 x y
       grind)
    | exact superpose eq1076 eq1893
    | (have j0 := eq1893 X0
       have j1 := eq1076 X0 y
       grind)
    | (have r₁ := eq1893 X0
       have r₂ := eq1076 x y
       grind)
    | exact resolve eq1893 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1893
  have eq34610 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq34609 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34609
  have eq34723 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op X0 X0)) y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq257 y X0
       have i₂ := eq34610 (σ y)
       grind)
    | exact superpose eq34610 eq257
    | exact resolve eq257 eq34610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq34610
  have eq34744 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34723 x
       have i₂ := eq781 x y
       grind)
    | exact superpose eq781 eq34723
    | exact resolve eq34723 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq34723
  have eq34780 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34744
       have i₂ := eq575 y
       grind)
    | exact superpose eq575 eq34744
    | exact resolve eq34744 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq34744
  have eq34791 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34780
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34780
    | exact resolve eq34780 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34780
  have eq34792 : y = (M.op y y) := by grind
  clear eq34791
  have eq34954 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq34792
       grind)
    | exact superpose eq34792 eq22
    | exact resolve eq22 eq34792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq35003 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1319 y X0
       have i₂ := eq34792
       grind)
    | exact superpose eq34792 eq1319
    | exact resolve eq1319 eq34792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319 eq34792
  have eq38866 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq35003 (σ x)
       grind)
    | exact superpose eq35003 eq14
    | exact resolve eq14 eq35003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35003
  have eq38889 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq38866
       have i₂ := eq34954 x
       grind)
    | exact superpose eq34954 eq38866
    | exact resolve eq38866 eq34954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34954 eq38866
  have eq38890 : False := by grind
  exact eq38890

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxy_pyx_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq11
    | (have r₁ := eq11 X0 (M.op X1 X0)
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq37 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq30
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq39 (τ X0) X1
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq64 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq80 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq22
    | (have j1 := eq41 X0 X0
       grind)
    | exact resolve eq22 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) (σ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq21
    | (have j1 := eq41 (k X0 X1) X0
       grind)
    | exact resolve eq21 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq11
    | (have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X0)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq132 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (k X0 (τ X1)) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq57
    | exact resolve eq57 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op X1 (σ X0))
       have i₂ := eq30 (σ X0) X1
       grind)
    | exact superpose eq30 eq57
    | exact resolve eq57 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq161
    | exact resolve eq161 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq319 : ∀ X0 X1 : G, (k X0 (τ (σ (k X0 X1)))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X0 (σ X1)
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq173
    | (have j1 := eq41 X1 X0
       grind)
    | exact resolve eq173 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq173
  have eq331 : ∀ X0 X1 : G, (k X0 (k X0 X1)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq319
    | (have j0 := eq319 X0 X1
       grind)
    | exact resolve eq319 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq456 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op (τ X1) X0) X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq57
    | (have j1 := eq52 X1 X0
       grind)
    | exact resolve eq57 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq57
  have eq483 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq481 X0 X1 X2
       have i₂ := eq158 X0 X1 X2
       grind)
    | exact superpose eq158 eq481
    | (have j0 := eq481 X0 X1 X2
       grind)
    | exact resolve eq481 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq481
  have eq494 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq456
    | (have j0 := eq456 X0 X1
       grind)
    | exact resolve eq456 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq532 : ∀ X0 X1 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq80
    | (have j0 := eq80 (τ X0) X1
       grind)
    | exact resolve eq80 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq80
  have eq554 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq559 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq667 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq14
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq14 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq699 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq667
    | (have j0 := eq667 X0 X1
       grind)
    | exact resolve eq667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq701 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq699
    | (have j0 := eq699 X0 X1
       grind)
    | exact resolve eq699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq699
  have eq754 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (τ X0) (τ X1)
       have i₂ := eq132 X1 X0
       grind)
    | exact superpose eq132 eq84
    | (have j0 := eq84 (τ X0) (τ (k X0 X1))
       grind)
    | exact resolve eq84 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq774 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq754
    | (have j0 := eq754 X0 X1
       grind)
    | exact resolve eq754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq781 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq774
    | (have j0 := eq774 X0 X1
       grind)
    | exact resolve eq774 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq782 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq781
    | (have j0 := eq781 X0 X1
       grind)
    | exact resolve eq781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq783 : ∀ X0 X1 : G, (M.op X0 (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq782 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq782
    | (have j0 := eq782 X0 X1
       grind)
    | exact resolve eq782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq1676 : ∀ X0 X1 : G, (k X1 X1) = (k (k X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq30 (k X1 X1) X0
       have i₂ := eq559 X1 X0
       grind)
    | exact superpose eq559 eq30
    | (have j1 := eq559 X1 X1
       grind)
    | exact resolve eq30 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq559
  have eq1839 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq783 X0 (σ (M.op X1 X1))
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq783
    | (have j0 := eq783 X0 X0
       grind)
    | exact resolve eq783 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq3128 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq701
    | exact resolve eq701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq3297 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3128 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128
  have eq3829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq674
       have i₂ := eq494 x y
       grind)
    | exact superpose eq494 eq674
    | (have j1 := eq494 x y
       grind)
    | (have r₁ := eq674
       have r₂ := eq494 x y
       grind)
    | exact resolve eq674 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq674
  have eq3830 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq3829
  have eq4072 : (M.op x y) = (τ (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq3830
       grind)
    | exact superpose eq3830 eq9
    | exact resolve eq9 eq3830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3830
  have eq4123 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4072
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq4072
    | exact resolve eq4072 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4072
  have eq4235 : y ≠ y ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq4123
       grind)
    | exact superpose eq4123 eq11
    | (have r₁ := eq11 y x
       have r₂ := eq4123
       grind)
    | exact resolve eq11 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4123
  have eq4237 : y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq4235
  have eq4238 : y = (k y x) := by
    first
    | (have j1 := eq3297 y x
       grind)
    | (have r₁ := eq4237
       have r₂ := eq3297 y x
       grind)
    | exact resolve eq4237 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq4237
  have eq4339 : y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq783 y x
       have i₂ := eq4238
       grind)
    | exact superpose eq4238 eq783
    | (have j0 := eq783 y y
       grind)
    | exact resolve eq783 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq4745 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq4339
       grind)
    | exact superpose eq4339 eq38
    | exact resolve eq38 eq4339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339
  have eq5287 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq4745 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4745
  have eq5288 : y = (M.op y x) := by grind
  clear eq5287
  have eq5339 : x = (M.op x y) := by
    first
    | (have i₁ := eq21 x y
       have i₂ := eq5288
       grind)
    | exact superpose eq5288 eq21
    | exact resolve eq21 eq5288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5288
  have eq17412 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op X0 (σ (M.op X2 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq1839 X0 X1
       grind)
    | exact superpose eq1839 eq38
    | (have j1 := eq1839 X0 X2
       grind)
    | exact resolve eq38 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1839
  have eq20695 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq17412 X0 (σ (M.op X1 X1)) X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17412
  have eq20696 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq20695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20695
  have eq44944 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 (τ X0) X0 X1
       have i₂ := eq1676 (τ X1) (τ X0)
       grind)
    | exact superpose eq1676 eq483
    | (have j0 := eq483 (τ X0) X0 x
       have j1 := eq1676 X0 (τ X0)
       grind)
    | exact resolve eq483 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq1676
  have eq45051 : ∀ X0 X1 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq44944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44944
  have eq45068 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45051 X0 x
       have i₂ := eq45 (τ x) (τ X0)
       grind)
    | exact superpose eq45 eq45051
    | (have j0 := eq45051 X0 x
       grind)
    | exact resolve eq45051 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq45051
  have eq45096 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq45068 X0
       have j1 := eq11 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq45068 X0
       have r₂ := eq11 (τ X0) (τ X0)
       grind)
    | exact resolve eq45068 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45068
  have eq45122 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45096 X0
       have i₂ := eq132 X0 X0
       grind)
    | exact superpose eq132 eq45096
    | exact resolve eq45096 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq45096
  have eq45518 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq45122 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45122
    | exact resolve eq45122 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45122
  have eq45721 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq45518 X0
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq45518
    | exact resolve eq45518 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq45518
  have eq45746 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq45721 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq45721
    | exact resolve eq45721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45721
  have eq176752 : y = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq331 y x
       have i₂ := eq4238
       grind)
    | exact superpose eq4238 eq331
    | (have j0 := eq331 y x
       grind)
    | exact resolve eq331 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq4238
  have eq177183 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq176752
       have i₂ := eq45746 y
       grind)
    | exact superpose eq45746 eq176752
    | exact resolve eq176752 eq45746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45746 eq176752
  have eq177512 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq21 (σ x) (σ y)
       have i₂ := eq177183
       grind)
    | exact superpose eq177183 eq21
    | exact resolve eq21 eq177183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq177183
  have eq178078 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq177512
       grind)
    | exact superpose eq177512 eq14
    | exact resolve eq14 eq177512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177512
  have eq178118 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq178078
       have i₂ := eq5339
       grind)
    | exact superpose eq5339 eq178078
    | exact resolve eq178078 eq5339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5339 eq178078
  have eq178119 : y = (M.op y y) := by grind
  clear eq178118
  have eq179122 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq178119
       grind)
    | exact superpose eq178119 eq22
    | exact resolve eq22 eq178119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq179168 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq20696 X0 y
       have i₂ := eq178119
       grind)
    | exact superpose eq178119 eq20696
    | exact resolve eq20696 eq178119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20696 eq178119
  have eq187557 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq179168 (σ x)
       grind)
    | exact superpose eq179168 eq14
    | exact resolve eq14 eq179168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179168
  have eq187631 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq187557
       have i₂ := eq179122 x
       grind)
    | exact superpose eq179122 eq187557
    | exact resolve eq187557 eq179122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179122 eq187557
  have eq187632 : False := by grind
  exact eq187632

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyx_pxy_Equation434 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq21 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq8 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X0) X0
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X0)
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq11
    | (have j0 := eq11 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X1 X0)
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq30
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (M.op X1 X1) X0
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq40 X0 X1
       grind)
    | (have i₁ := eq41 (M.op X1 X1) X1
       have i₂ := eq40 X0 (M.op X1 X1)
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X1) X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X0) X0
       have r₂ := eq24 X0 X1
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq54 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq54
    | exact resolve eq54 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq16
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq16 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq14
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq22
    | (have j1 := eq44 X0 X0
       grind)
    | exact resolve eq22 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X1) (σ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq21
    | (have j1 := eq44 X1 (k X0 X1)
       grind)
    | exact resolve eq21 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq95 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (M.op X0 X0) X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq32
    | exact resolve eq32 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq122 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X1 X1)
       have i₂ := eq95 (τ X0) X1
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq123 : ∀ X0 X1 : G, (k (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq122 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq122
    | exact resolve eq122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq137 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (σ (M.op X1 X1))
       have i₂ := eq123 (τ X0) X1
       grind)
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq138 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq137
    | exact resolve eq137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq139 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20
    | exact resolve eq20 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq20
    | exact resolve eq20 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 (σ X0)) X0
       have i₂ := eq55 X1 (σ X0)
       grind)
    | exact superpose eq55 eq20
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq145
    | exact resolve eq145 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq246 : ∀ X0 X1 : G, (k (τ (σ (k X0 X1))) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X1 (σ X0)
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq151
    | (have j1 := eq44 X0 X1
       grind)
    | exact resolve eq151 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq258 : ∀ X0 X1 : G, (k (k X0 X1) X1) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq246 X0 X1
       have i₂ := eq9 (k X0 X1)
       grind)
    | exact superpose eq9 eq246
    | (have j0 := eq246 X0 X1
       grind)
    | exact resolve eq246 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq503 : ∀ X0 X1 X2 : G, (τ (k X2 (k (σ X0) X1))) = (k (τ X2) (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X2 (M.op X0 (τ X1))
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq20
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq20 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq513 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (k (τ X2) (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X0 X1 X2
       have i₂ := eq141 X0 X1 X2
       grind)
    | exact superpose eq141 eq503
    | (have j0 := eq503 X0 X1 X2
       grind)
    | exact resolve eq503 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq503
  have eq568 : ∀ X0 X1 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq81
    | (have j0 := eq81 (τ X0) X1
       grind)
    | exact resolve eq81 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq81
  have eq590 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq568
    | (have j0 := eq568 X0 X1
       grind)
    | exact resolve eq568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq595 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq703 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq80
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq80
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq704 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq703
  have eq851 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (τ X0) (τ X1)
       have i₂ := eq139 X1 X0
       grind)
    | exact superpose eq139 eq86
    | (have j0 := eq86 (τ X1) (τ (k X0 X1))
       grind)
    | exact resolve eq86 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq870 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) (k X0 X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq878 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq870
    | (have j0 := eq870 X0 X1
       grind)
    | exact resolve eq870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq879 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 (k X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq878 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq878
    | (have j0 := eq878 X0 X1
       grind)
    | exact resolve eq878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq880 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq879 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq879
    | (have j0 := eq879 X0 X1
       grind)
    | exact resolve eq879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1509 : ∀ X0 X1 : G, (k X1 X1) = (k X0 (k X1 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (k X1 X1)
       have i₂ := eq595 X1 X0
       grind)
    | exact superpose eq595 eq55
    | (have j1 := eq595 X1 X1
       grind)
    | exact resolve eq55 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq1922 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq151 y (σ x)
       have i₂ := eq704
       grind)
    | exact superpose eq704 eq151
    | exact resolve eq151 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq704
  have eq1932 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1922
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq1922
    | exact resolve eq1922 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1922
  have eq2063 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq880 x y
       have i₂ := eq1932
       grind)
    | exact superpose eq1932 eq880
    | (have j0 := eq880 y y
       grind)
    | exact resolve eq880 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq1932
  have eq2064 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq2063
  have eq2193 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq2064
       grind)
    | exact superpose eq2064 eq22
    | exact resolve eq22 eq2064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2064
  have eq2469 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq2193 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2470 : x = (M.op x y) := by grind
  clear eq2469
  have eq2574 : y = (k x y) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq2470
       grind)
    | exact superpose eq2470 eq55
    | exact resolve eq55 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq11841 : ∀ X0 X1 : G, (k (τ X1) (τ X1)) = (k (τ X0) (M.op (τ X1) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1509 (τ X0) (τ X1)
       have i₂ := eq513 (τ X1) X1 X0
       grind)
    | exact superpose eq513 eq1509
    | (have j0 := eq1509 X0 (τ X1)
       have j1 := eq513 (τ X1) X1 x
       grind)
    | exact resolve eq1509 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq1509
  have eq11912 : ∀ X0 X1 : G, (k (τ X1) (τ X1)) = (k (τ X0) (M.op (τ X1) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq11841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11841
  have eq11930 : ∀ X1 : G, (k (τ X1) (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X1)) := by
    intro X1
    first
    | (have i₁ := eq11912 x X1
       have i₂ := eq42 (τ x) (τ X1)
       grind)
    | exact superpose eq42 eq11912
    | (have j0 := eq11912 x X1
       grind)
    | exact resolve eq11912 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq11912
  have eq11947 : ∀ X1 : G, (k (τ X1) (τ X1)) = (M.op (τ X1) (τ X1)) := by
    intro X1
    first
    | (have j0 := eq11930 X1
       have j1 := eq11 (τ X1) (τ X1)
       grind)
    | (have r₁ := eq11930 X1
       have r₂ := eq11 (τ X1) (τ X1)
       grind)
    | exact resolve eq11930 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11930
  have eq11962 : ∀ X1 : G, (τ (k X1 X1)) = (M.op (τ X1) (τ X1)) := by
    intro X1
    first
    | (have i₁ := eq11947 X1
       have i₂ := eq139 X1 X1
       grind)
    | exact superpose eq139 eq11947
    | exact resolve eq11947 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq11947
  have eq12127 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq11962 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq11962
    | exact resolve eq11962 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12143 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ X0) X1
       have i₂ := eq11962 X0
       grind)
    | exact superpose eq11962 eq22
    | exact resolve eq22 eq11962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11962
  have eq12195 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq12127 X0
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq12127
    | exact resolve eq12127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12127
  have eq12202 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12195 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq12195
    | exact resolve eq12195 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq13589 : ∀ X0 X1 : G, (M.op X1 (τ (σ (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12143 (σ (σ (M.op X0 X0))) X1
       have i₂ := eq138 (σ (σ (M.op X0 X0))) X0
       grind)
    | exact superpose eq138 eq12143
    | exact resolve eq12143 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq12143
  have eq13674 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13589 X0 X1
       have i₂ := eq9 (σ (M.op X0 X0))
       grind)
    | exact superpose eq9 eq13589
    | exact resolve eq13589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13589
  have eq60213 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq258 x y
       have i₂ := eq2574
       grind)
    | exact superpose eq2574 eq258
    | (have j0 := eq258 x y
       grind)
    | exact resolve eq258 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq2574
  have eq60458 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq60213
       have i₂ := eq12202 y
       grind)
    | exact superpose eq12202 eq60213
    | exact resolve eq60213 eq12202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12202 eq60213
  have eq62477 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq60458
       grind)
    | exact superpose eq60458 eq14
    | exact resolve eq14 eq60458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60458
  have eq62494 : (σ x) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq62477
       have i₂ := eq2470
       grind)
    | exact superpose eq2470 eq62477
    | exact resolve eq62477 eq2470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470 eq62477
  have eq62495 : y = (M.op y y) := by grind
  clear eq62494
  have eq62855 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq62495
       grind)
    | exact superpose eq62495 eq22
    | exact resolve eq22 eq62495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq62892 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13674 y X0
       have i₂ := eq62495
       grind)
    | exact superpose eq62495 eq13674
    | exact resolve eq13674 eq62495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13674 eq62495
  have eq69604 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62892 (σ x)
       grind)
    | exact superpose eq62892 eq14
    | exact resolve eq14 eq62892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62892
  have eq69606 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq69604
       have i₂ := eq62855 x
       grind)
    | exact superpose eq62855 eq69604
    | exact resolve eq69604 eq62855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62855 eq69604
  have eq69607 : False := by grind
  exact eq69607

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation434 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9
    | exact resolve eq9 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq44 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq61 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq218 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq42 X2 X0
       grind)
    | exact superpose eq42 eq22
    | (have j1 := eq42 X2 X0
       grind)
    | exact resolve eq22 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq269 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq61
    | exact resolve eq61 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) ≠ (k X0 (M.op X1 X1)) ∨ (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X1 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq102
    | exact resolve eq102 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq575 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq579 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq560 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq603 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq575 (σ X0)
       grind)
    | exact superpose eq575 eq13
    | exact resolve eq13 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq603 X0
       have i₂ := eq575 X0
       grind)
    | exact superpose eq575 eq603
    | exact resolve eq603 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq756 : ∀ X0 X1 : G, (τ (k (σ X0) (M.op X1 X1))) = (k (τ (σ X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X0
       have i₂ := eq579 (σ X0) X1
       grind)
    | exact superpose eq579 eq20
    | exact resolve eq20 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq579
  have eq760 : ∀ X0 X1 : G, (k X0 X0) = (τ (k (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq756
    | exact resolve eq756 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq781 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq760 X0 X1
       have i₂ := eq61 X0 (M.op X1 X1)
       grind)
    | exact superpose eq61 eq760
    | exact resolve eq760 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq760
  have eq970 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1045 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq970
    | (have j0 := eq970 X0 X1
       grind)
    | exact resolve eq970 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq1316 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq22
    | exact resolve eq22 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq1888 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq218 y X0 x
       grind)
    | exact superpose eq218 eq14
    | (have j1 := eq218 y X0 x
       grind)
    | exact resolve eq14 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq34307 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1888 X0
       have i₂ := eq1045 x y
       grind)
    | exact superpose eq1045 eq1888
    | (have j0 := eq1888 X0
       have j1 := eq1045 X0 y
       grind)
    | (have r₁ := eq1888 X0
       have r₂ := eq1045 x y
       grind)
    | exact resolve eq1888 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1888
  have eq34308 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq34307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34307
  have eq34418 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq269 y X0
       have i₂ := eq34308 (σ y)
       grind)
    | exact superpose eq34308 eq269
    | exact resolve eq269 eq34308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq34308
  have eq34439 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34418 x
       have i₂ := eq781 y x
       grind)
    | exact superpose eq781 eq34418
    | exact resolve eq34418 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq34418
  have eq34476 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34439
       have i₂ := eq575 y
       grind)
    | exact superpose eq575 eq34439
    | exact resolve eq34439 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq34439
  have eq34488 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq34476
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq34476
    | exact resolve eq34476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34476
  have eq34489 : y = (M.op y y) := by grind
  clear eq34488
  have eq34656 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq34489
       grind)
    | exact superpose eq34489 eq22
    | exact resolve eq22 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq34705 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1316 y X0
       have i₂ := eq34489
       grind)
    | exact superpose eq34489 eq1316
    | exact resolve eq1316 eq34489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316 eq34489
  have eq38564 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34705 (σ x)
       grind)
    | exact superpose eq34705 eq14
    | exact resolve eq14 eq34705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34705
  have eq38587 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq38564
       have i₂ := eq34656 x
       grind)
    | exact superpose eq34656 eq38564
    | exact resolve eq38564 eq34656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34656 eq38564
  have eq38588 : False := by grind
  exact eq38588

/-- `Equation436`: `x = x ◇ (y ◇ (y ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation436 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law436 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law436.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j0 := eq11 X0 X0
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq88 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq88 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92 (σ X0) (σ X1)
       grind)
    | exact superpose eq92 eq13
    | exact resolve eq13 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 X0 X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq108
  have eq1449 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq115 x y
       grind)
    | exact superpose eq115 eq14
    | (have r₁ := eq14
       have r₂ := eq115 x y
       grind)
    | exact resolve eq14 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1469 : False := by grind
  exact eq1469

/-- `Equation4385`: `x ◇ (x ◇ x) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pxx_pyx_Equation4385 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4385 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op x X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq9
    | exact resolve eq9 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0 (M.op x X0)
       have i₂ := eq8 X0 x
       grind)
    | exact superpose eq8 eq18
    | exact resolve eq18 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq12 X1 (σ X0)
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq76 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq82 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq38
  have eq103 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq76 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq19 X0
       grind)
    | exact superpose eq19 eq76
    | (have j0 := eq76 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq76 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq19 X0
       grind)
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq104 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq170 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq53 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq53
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq104
    | exact resolve eq104 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq30 X1 X0
       grind)
    | exact superpose eq30 eq9
    | (have j1 := eq30 X1 X0
       grind)
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (σ (k X1 X2)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq30 X2 X0
       grind)
    | exact superpose eq30 eq13
    | (have j1 := eq30 X2 X0
       grind)
    | exact resolve eq13 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq33
    | exact resolve eq33 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq683 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq734 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq1569 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq82
    | (have j1 := eq30 X0 X1
       grind)
    | exact resolve eq82 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq82
  have eq1610 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1569 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1569
    | (have j0 := eq1569 X0 X1
       grind)
    | exact resolve eq1569 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq2070 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op (σ X2) (σ X1)) = (σ (k X1 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq281 X1 X2
       have i₂ := eq281 X1 X0
       grind)
    | (have i₁ := eq281 X0 X1
       have i₂ := eq281 X0 (τ (M.op (σ X0) (σ X0)))
       grind)
    | exact superpose eq281 eq281
    | (have j0 := eq281 X1 X2
       have j1 := eq281 X1 X2
       grind)
    | exact resolve eq281 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2089 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq281
    | exact resolve eq281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2143 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2089 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq2089
    | (have j0 := eq2089 X0 X1
       grind)
    | exact resolve eq2089 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq2089
  have eq2155 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2143 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2143
    | (have j0 := eq2143 X1 (τ X0)
       grind)
    | exact resolve eq2143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2703 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1610 x y
       grind)
    | exact superpose eq1610 eq14
    | (have j1 := eq1610 x y
       grind)
    | exact resolve eq14 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2749 : x = (k y x) := by
    first
    | (have j1 := eq734 x y
       grind)
    | (have r₁ := eq2703
       have r₂ := eq734 x y
       grind)
    | exact resolve eq2703 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703
  have eq2892 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq683 x y
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq683
    | (have j0 := eq683 x y
       grind)
    | exact resolve eq683 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8911 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    grind
  clear eq283
  have eq14269 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64
    | exact resolve eq64 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq14611 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14269 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq14269
    | (have j0 := eq14269 X0 X1
       grind)
    | exact resolve eq14269 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14269
  have eq59249 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8911 (τ X1) (τ X0)
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq8911
    | exact resolve eq8911 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59661 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X1)
       have i₂ := eq8911 X0 X1
       grind)
    | exact superpose eq8911 eq9
    | (have j1 := eq8911 X0 X1
       grind)
    | exact resolve eq9 eq8911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60035 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq8911 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8911
  have eq60036 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq60035 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60035
  have eq60339 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (k X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59661 X0 X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq59661
    | (have j0 := eq59661 X0 X1
       grind)
    | exact resolve eq59661 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59661
  have eq60623 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (k (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq59249 X0 X1
       have i₂ := eq60036 (τ X0)
       grind)
    | exact superpose eq60036 eq59249
    | (have j0 := eq59249 X0 X1
       grind)
    | exact resolve eq59249 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59249
  have eq60862 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60339 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq60339
    | (have j0 := eq60339 X0 X1
       grind)
    | exact resolve eq60339 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60339
  have eq60982 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (σ (τ X0)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60623 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq60623
    | (have j0 := eq60623 X0 X1
       grind)
    | exact resolve eq60623 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60623
  have eq61157 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60982 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60982
    | (have j0 := eq60982 X0 X1
       grind)
    | exact resolve eq60982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60982
  have eq61240 : ∀ X0 X1 : G, (k X0 X1) = (k X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61157 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq61157
    | (have j0 := eq61157 X0 X1
       grind)
    | exact resolve eq61157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61157
  have eq61281 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61240 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61240
    | (have j0 := eq61240 X0 X1
       grind)
    | exact resolve eq61240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61240
  have eq61300 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61281 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq61281
    | (have j0 := eq61281 X0 X1
       grind)
    | exact resolve eq61281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61281
  have eq61305 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61300 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq61300
    | (have j0 := eq61300 X0 X1
       grind)
    | exact resolve eq61300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61300
  have eq61347 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60036 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq60036
    | exact resolve eq60036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61427 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq281
    | (have j0 := eq281 X0 X1
       grind)
    | exact resolve eq281 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq61449 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (M.op X1 (σ X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq8
    | exact resolve eq8 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61476 : ∀ X0 X1 : G, (τ X1) = (τ (σ (k X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 X1 (σ X0)
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq2155
    | (have j0 := eq2155 X1 (σ X0)
       grind)
    | exact resolve eq2155 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq61494 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8 (σ X0) (σ X0)
       have i₂ := eq60036 X0
       grind)
    | exact superpose eq60036 eq8
    | exact resolve eq8 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61556 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61476 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq61476
    | (have j0 := eq61476 X0 X1
       grind)
    | exact resolve eq61476 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61476
  have eq61577 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61427 X0 X1
       have i₂ := eq9 (k X0 X0)
       grind)
    | exact superpose eq9 eq61427
    | (have j0 := eq61427 X0 X1
       grind)
    | exact resolve eq61427 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61427
  have eq61620 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq61347 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq61347
    | exact resolve eq61347 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq61347
  have eq61663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq61620 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61620
    | exact resolve eq61620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61620
  have eq63339 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 X0
       have i₂ := eq61663 (τ X0)
       grind)
    | exact superpose eq61663 eq61
    | exact resolve eq61 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63391 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq63339 X0
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq63339
    | exact resolve eq63339 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63339
  have eq78681 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61663 X0
       have i₂ := eq61305 X0 X1
       grind)
    | (have i₁ := eq61663 X1
       have i₂ := eq61305 X1 X1
       grind)
    | exact superpose eq61305 eq61663
    | (have j1 := eq61305 X0 X1
       grind)
    | exact resolve eq61663 eq61305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78795 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78796 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61305 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61305
  have eq78797 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78796 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78796
    | (have j0 := eq78796 X0 X1
       grind)
    | (have r₁ := eq78796 X0 X0
       have r₂ := eq61663 X0
       grind)
    | exact resolve eq78796 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78796
  have eq78798 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq78795 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78795
    | (have j0 := eq78795 X0 X1
       grind)
    | (have r₁ := eq78795 X0 X0
       have r₂ := eq61663 X0
       grind)
    | exact resolve eq78795 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78795
  have eq79155 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq78798 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq78798
    | (have j0 := eq78798 X0 X1
       grind)
    | exact resolve eq78798 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78798
  have eq87714 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61449 X0 X1
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq61449
    | exact resolve eq61449 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61449
  have eq88129 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq61494 X0
       have i₂ := eq61663 X0
       grind)
    | exact superpose eq61663 eq61494
    | exact resolve eq61494 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61494
  have eq88916 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq61556 X1 (σ X0)
       grind)
    | exact superpose eq61556 eq13
    | (have j1 := eq61556 X1 (σ X0)
       grind)
    | exact resolve eq13 eq61556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61556
  have eq88958 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88916 X0 X1
       have i₂ := eq61663 X1
       grind)
    | exact superpose eq61663 eq88916
    | (have j0 := eq88916 X0 X1
       grind)
    | exact resolve eq88916 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88916
  have eq89077 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88958 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq88958
    | (have j0 := eq88958 X0 X1
       grind)
    | exact resolve eq88958 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88958
  have eq89277 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq61577 y x
       grind)
    | exact superpose eq61577 eq14
    | (have j1 := eq61577 y x
       grind)
    | exact resolve eq14 eq61577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61577
  have eq89389 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq89277
       have i₂ := eq2749
       grind)
    | exact superpose eq2749 eq89277
    | exact resolve eq89277 eq2749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749 eq89277
  have eq89452 : x = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq89389
       have i₂ := eq61663 y
       grind)
    | exact superpose eq61663 eq89389
    | exact resolve eq89389 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89389
  have eq89488 : x = (M.op y y) := by
    first
    | (have r₁ := eq89452
       have r₂ := eq2892
       grind)
    | exact resolve eq89452 eq2892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892 eq89452
  have eq89560 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq8
    | exact resolve eq8 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89566 : (M.op x y) = (M.op (M.op y x) y) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq53
    | exact resolve eq53 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq89584 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq230 y y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq230
    | exact resolve eq230 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq89725 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq79155 x y
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq79155
    | (have j0 := eq79155 x y
       grind)
    | exact resolve eq79155 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89843 : (M.op y (M.op y x)) = (M.op (M.op x y) (M.op y x)) ∨ (M.op y (M.op y x)) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq170 y (M.op y x)
       have i₂ := eq89566
       grind)
    | exact superpose eq89566 eq170
    | (have j0 := eq170 y (M.op y x)
       grind)
    | exact resolve eq170 eq89566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq89872 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op y (M.op y x)) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq89843
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq89843
    | exact resolve eq89843 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89843
  have eq89888 : (M.op y (M.op x y)) = (k (M.op x y) y) ∨ (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq89872
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq89872
    | exact resolve eq89872 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89872
  have eq89898 : (M.op y (M.op x y)) = (k (M.op x y) y) := by
    first
    | (have j1 := eq78797 (M.op x y) y
       grind)
    | (have r₁ := eq89888
       have r₂ := eq78797 (M.op x y) y
       grind)
    | exact resolve eq89888 eq78797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78797 eq89888
  have eq94517 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq88129 y
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq88129
    | exact resolve eq88129 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88129
  have eq94695 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1610 y x
       have i₂ := eq94517
       grind)
    | exact superpose eq94517 eq1610
    | (have j0 := eq1610 y x
       grind)
    | exact resolve eq1610 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq95588 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (σ (k X1 X2)) = (σ (M.op X2 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq683 X2 X1
       have i₂ := eq89077 X0 X1
       grind)
    | (have i₁ := eq683 X0 X1
       have i₂ := eq89077 (M.op X1 X1) X1
       grind)
    | exact superpose eq89077 eq683
    | (have j0 := eq683 X2 X1
       have j1 := eq89077 X0 X1
       grind)
    | exact resolve eq683 eq89077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89077
  have eq97472 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = X0 ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq2070 x y X0
       grind)
    | exact superpose eq2070 eq14
    | (have j1 := eq2070 x y X0
       grind)
    | (have r₁ := eq14
       have r₂ := eq2070 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2070 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq97478 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq97472 X0
       have j1 := eq95588 (σ (k y X0)) x (M.op (σ X0) (σ y))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 (σ (k y x)) x (σ (M.op x y))
       grind)
    | (have r₁ := eq97472 X0
       have r₂ := eq95588 X0 y x
       grind)
    | exact resolve eq97472 eq95588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95588 eq97472
  have eq97575 : ∀ X0 : G, (M.op (σ (k y X0)) (σ y)) = (M.op (σ y) (σ (M.op y y))) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq87714 y (σ X0)
       have i₂ := eq97478 X0
       grind)
    | exact superpose eq97478 eq87714
    | (have j1 := eq97478 X0
       grind)
    | exact resolve eq87714 eq97478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87714 eq97478
  have eq97656 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97575 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq97575
    | (have j0 := eq97575 X0
       grind)
    | exact resolve eq97575 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97575
  have eq97710 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k y X0)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97656 X0
       have i₂ := eq94517
       grind)
    | exact superpose eq94517 eq97656
    | (have j0 := eq97656 X0
       grind)
    | exact resolve eq97656 eq94517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94517 eq97656
  have eq100781 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq94695
       grind)
    | exact superpose eq94695 eq14
    | exact resolve eq14 eq94695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94695
  have eq100886 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100781
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq100781
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq100781 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100898 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq100781
       have i₂ := eq734 y x
       grind)
    | exact superpose eq734 eq100781
    | (have j1 := eq734 y x
       grind)
    | exact resolve eq100781 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq100781
  have eq100904 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k x y) := by grind
  clear eq100898
  have eq100910 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq100904
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100904
    | exact resolve eq100904 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100904
  have eq100911 : y = (k x y) := by grind
  clear eq100910
  have eq100930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100886
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100886
    | exact resolve eq100886 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100886
  have eq100931 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq100930
  have eq100941 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100931
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100931
    | exact resolve eq100931 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100931
  have eq100992 : (τ y) = (τ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14611 y x
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq14611
    | (have j0 := eq14611 y x
       grind)
    | exact resolve eq14611 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14611
  have eq101008 : (τ y) = (τ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq100992
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq100992
    | exact resolve eq100992 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100992
  have eq101124 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8 y x
       have i₂ := eq100941
       grind)
    | exact superpose eq100941 eq8
    | exact resolve eq8 eq100941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100941
  have eq101168 : x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101124
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq101124
    | exact resolve eq101124 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101124
  have eq101186 : x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101168
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq101168
    | exact resolve eq101168 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101168
  have eq101410 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89725
       have i₂ := eq101186
       grind)
    | exact superpose eq101186 eq89725
    | exact resolve eq89725 eq101186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89725
  have eq101467 : y = (M.op x x) ∨ x ≠ (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101410
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq101410
    | exact resolve eq101410 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101410
  have eq101468 : x ≠ (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq101467
  have eq101765 : (σ (M.op (τ y) (τ y))) = (k (M.op x y) (σ (M.op (τ y) (τ y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21 (M.op x y)
       have i₂ := eq101008
       grind)
    | exact superpose eq101008 eq21
    | exact resolve eq21 eq101008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq101008
  have eq101805 : (σ (τ (M.op y y))) = (k (M.op x y) (σ (τ (M.op y y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101765
       have i₂ := eq63391 y
       grind)
    | exact superpose eq63391 eq101765
    | exact resolve eq101765 eq63391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63391 eq101765
  have eq101815 : (M.op y y) = (k (M.op x y) (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101805
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq101805
    | exact resolve eq101805 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101805
  have eq101818 : x = (k (M.op x y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101815
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq101815
    | exact resolve eq101815 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101815
  have eq103037 : x = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq101818
       have i₂ := eq101186
       grind)
    | exact superpose eq101186 eq101818
    | exact resolve eq101818 eq101186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101186 eq101818
  have eq103049 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq103037
  have eq103054 : x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103049
       have i₂ := eq61663 x
       grind)
    | exact superpose eq61663 eq103049
    | exact resolve eq103049 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103049
  have eq103055 : y = (M.op x x) := by
    first
    | (have r₁ := eq103054
       have r₂ := eq101468
       grind)
    | exact resolve eq103054 eq101468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101468 eq103054
  have eq112125 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq97710 X0
       have i₂ := eq683 X0 y
       grind)
    | exact superpose eq683 eq97710
    | (have j0 := eq97710 X0
       have j1 := eq683 X0 y
       grind)
    | exact resolve eq97710 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq97710
  have eq112221 : ∀ X0 : G, x = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq112125 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq112125
    | (have j0 := eq112125 X0
       grind)
    | exact resolve eq112125 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112125
  have eq112222 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ y)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq112221 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112221
  have eq119914 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60862 X0 X1
       have i₂ := eq78681 X0 X1
       grind)
    | exact superpose eq78681 eq60862
    | (have j1 := eq78681 X1 X0
       grind)
    | exact resolve eq60862 eq78681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60862 eq78681
  have eq120099 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq119914 X0 X1
       have i₂ := eq61663 X1
       grind)
    | exact superpose eq61663 eq119914
    | (have j0 := eq119914 X0 X1
       grind)
    | exact resolve eq119914 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119914
  have eq120145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq120099 X0 X1
       have j1 := eq79155 X1 X0
       grind)
    | (have r₁ := eq120099 X1 X0
       have r₂ := eq79155 X0 X1
       grind)
    | (have r₁ := eq120099 X0 X0
       have r₂ := eq79155 X0 X0
       grind)
    | exact resolve eq120099 eq79155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79155 eq120099
  have eq127955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op (M.op X0 y) y)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq112222 X0
       have i₂ := eq120145 (M.op X0 y) y
       grind)
    | exact superpose eq120145 eq112222
    | (have j0 := eq112222 X0
       have j1 := eq120145 (M.op X0 y) y
       grind)
    | exact resolve eq112222 eq120145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112222 eq120145
  have eq128140 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq127955 X0
       have i₂ := eq8 y X0
       grind)
    | exact superpose eq8 eq127955
    | (have j0 := eq127955 X0
       grind)
    | exact resolve eq127955 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127955
  have eq128192 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq128140 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128140
    | (have j0 := eq128140 X0
       grind)
    | exact resolve eq128140 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128140
  have eq128212 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq128192 X0
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq128192
    | (have j0 := eq128192 X0
       grind)
    | exact resolve eq128192 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128192
  have eq128220 : ∀ X0 : G, x = X0 ∨ (M.op y y) = (k y (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq128212 X0
       grind)
    | (have r₁ := eq128212 X0
       have r₂ := eq14
       grind)
    | exact resolve eq128212 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128212
  have eq128222 : ∀ X0 : G, x = (k y (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq128220 X0
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128220
    | (have j0 := eq128220 (k y (M.op X0 y))
       grind)
    | exact resolve eq128220 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128220
  have eq128239 : x = (k y (M.op y (M.op y y))) ∨ x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq128222 (M.op y (M.op y y))
       have i₂ := eq19 y
       grind)
    | exact superpose eq19 eq128222
    | (have j0 := eq128222 (k y (M.op y (M.op y y)))
       grind)
    | exact resolve eq128222 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq128279 : x = (k y (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq128222 (M.op y x)
       have i₂ := eq89566
       grind)
    | exact superpose eq89566 eq128222
    | (have j0 := eq128222 x
       grind)
    | exact resolve eq128222 eq89566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89566 eq128222
  have eq128487 : x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq128279
       have i₂ := eq89584
       grind)
    | exact superpose eq89584 eq128279
    | exact resolve eq128279 eq89584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89584 eq128279
  have eq128515 : x = (M.op y (M.op y y)) ∨ x = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq128239
       have i₂ := eq104 y
       grind)
    | exact superpose eq104 eq128239
    | exact resolve eq128239 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq128239
  have eq128516 : x = (M.op y (M.op y y)) := by grind
  clear eq128515
  have eq128611 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128487
       have i₂ := eq89560
       grind)
    | exact superpose eq89560 eq128487
    | exact resolve eq128487 eq89560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89560 eq128487
  have eq128612 : x = (M.op x y) := by grind
  clear eq128611
  have eq128641 : x = (M.op y x) := by
    first
    | (have i₁ := eq128516
       have i₂ := eq89488
       grind)
    | exact superpose eq89488 eq128516
    | exact resolve eq128516 eq89488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89488 eq128516
  have eq128779 : (M.op y x) = (k x y) := by
    first
    | (have i₁ := eq89898
       have i₂ := eq128612
       grind)
    | exact superpose eq128612 eq89898
    | exact resolve eq89898 eq128612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89898 eq128612
  have eq128963 : y = (M.op y x) := by
    first
    | (have i₁ := eq128779
       have i₂ := eq100911
       grind)
    | exact superpose eq100911 eq128779
    | exact resolve eq128779 eq100911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100911 eq128779
  have eq129005 : x = y := by
    first
    | (have i₁ := eq128963
       have i₂ := eq128641
       grind)
    | exact superpose eq128641 eq128963
    | exact resolve eq128963 eq128641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128641 eq128963
  have eq129053 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq129005
       grind)
    | exact superpose eq129005 eq14
    | exact resolve eq14 eq129005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129005
  have eq129287 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq129053
       have i₂ := eq103055
       grind)
    | exact superpose eq103055 eq129053
    | exact resolve eq129053 eq103055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129053
  have eq129312 : (σ y) ≠ (σ (k x x)) := by
    first
    | (have i₁ := eq129287
       have i₂ := eq60036 x
       grind)
    | exact superpose eq60036 eq129287
    | exact resolve eq129287 eq60036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60036 eq129287
  have eq129321 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq129312
       have i₂ := eq61663 x
       grind)
    | exact superpose eq61663 eq129312
    | exact resolve eq129312 eq61663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61663 eq129312
  have eq129325 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq129321
       have i₂ := eq103055
       grind)
    | exact superpose eq103055 eq129321
    | exact resolve eq129321 eq103055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103055 eq129321
  have eq129326 : False := by grind
  exact eq129326

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pyx_Equation4386 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4386 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht he hd nh hM hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13
    | exact resolve eq13 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X1 X0)
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X1) X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 X1 (τ X0)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X2 X1 X0
       grind)
    | (have i₁ := eq8 X2 (M.op X2 X1)
       have i₂ := eq18 X0 X1 X2
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq29
    | exact resolve eq29 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq39
  have eq123 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq135 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq12 X0 (M.op X1 X0)
       grind)
    | exact superpose eq12 eq19
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq19 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq77 (M.op X1 X1) X1
       have i₂ := eq8 X1 X0
       grind)
    | exact superpose eq8 eq77
    | (have j0 := eq77 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq77 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X0)
       have r₂ := eq8 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq77 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = X2 ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 (k X1 X1)
       have j1 := eq28 X2 X1 X2
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X2) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op X1 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq28 X1 X1 X0
       grind)
    | exact superpose eq28 eq8
    | (have j1 := eq28 (M.op (M.op X0 X1) X0) X1 X2
       grind)
    | exact resolve eq8 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq28 eq13
    | (have j1 := eq28 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq298 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq31
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq123
    | (have j1 := eq31 X0 X1
       grind)
    | exact resolve eq123 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq352 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq335
    | (have j0 := eq335 X0 X1
       grind)
    | exact resolve eq335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq1125 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1223 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1125 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1125
    | (have j0 := eq1125 X0 X1
       grind)
    | exact resolve eq1125 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1475 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq2335 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq71 X0 X0
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2775 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (τ (σ X0)) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X1 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq325
    | (have j0 := eq325 X1 X0
       have j1 := eq31 X0 X1
       grind)
    | exact resolve eq325 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq325
  have eq2826 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2775 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2775
    | (have j0 := eq2775 X0 X1
       grind)
    | exact resolve eq2775 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq7029 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X0
       have i₂ := eq184 X1 X0 X0
       grind)
    | exact superpose eq184 eq135
    | (have j0 := eq135 X0 X0
       have j1 := eq184 X0 X0 x
       grind)
    | exact resolve eq135 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq7123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X1 X0) X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq7029 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7029
  have eq11751 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq14
    | (have j1 := eq352 x y
       grind)
    | exact resolve eq14 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11859 : y = (k y x) := by
    first
    | (have j1 := eq1475 x y
       grind)
    | (have r₁ := eq11751
       have r₂ := eq1475 x y
       grind)
    | exact resolve eq11751 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11751
  have eq12166 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq183 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq12167 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12166 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12166
  have eq12265 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1223 x y
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq1223
    | (have j0 := eq1223 x y
       grind)
    | exact resolve eq1223 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13658 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (M.op (M.op X1 (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq211 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq14586 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq184 X2 X0 x
       have i₂ := eq12167 X0 x
       grind)
    | exact superpose eq12167 eq184
    | (have j0 := eq184 X0 X0 X2
       have j1 := eq12167 X0 x
       grind)
    | exact resolve eq184 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq14707 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X2 X0) X2)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X2
    first
    | (have j0 := eq14586 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14586
  have eq58255 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq149 X0 X1
       have i₂ := eq12 X0 (M.op X0 X1)
       grind)
    | exact superpose eq12 eq149
    | (have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq149 X0 X0
       have r₂ := eq12 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq149 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq70258 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq2826 x y
       grind)
    | exact superpose eq2826 eq14
    | (have j1 := eq2826 x y
       grind)
    | (have r₁ := eq14
       have r₂ := eq2826 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq14
       have r₂ := eq2826 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq2826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq70265 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y := by
    first
    | (have i₁ := eq70258
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq70258
    | exact resolve eq70258 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70258
  have eq70532 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70265
       have i₂ := eq12265
       grind)
    | exact superpose eq12265 eq70265
    | (have r₁ := eq70265
       have r₂ := eq12265
       grind)
    | exact resolve eq70265 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70265
  have eq70533 : (σ x) = (σ (k y y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq70532
  have eq70588 : (k y y) = (τ (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq9 (k y y)
       have i₂ := eq70533
       grind)
    | exact superpose eq70533 eq9
    | exact resolve eq9 eq70533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70533
  have eq70599 : x = (k y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70588
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq70588
    | exact resolve eq70588 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70588
  have eq70700 : x = (M.op y y) ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29 y y
       have i₂ := eq70599
       grind)
    | exact superpose eq70599 eq29
    | exact resolve eq29 eq70599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq70599
  have eq70730 : x = (M.op y y) ∨ x = y := by grind
  clear eq70700
  have eq70967 : x = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq7123 y y
       have i₂ := eq70730
       grind)
    | exact superpose eq70730 eq7123
    | exact resolve eq7123 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq70973 : y = (M.op y (M.op x y)) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq14707 y y
       have i₂ := eq70730
       grind)
    | exact superpose eq70730 eq14707
    | exact resolve eq14707 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14707
  have eq75777 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13658 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13658
    | exact resolve eq13658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13658
  have eq75783 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75777 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq75777
    | (have j0 := eq75777 X0 X1
       grind)
    | exact resolve eq75777 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75777
  have eq75784 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq75783 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75783
    | (have j0 := eq75783 X0 X1
       grind)
    | exact resolve eq75783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75783
  have eq75785 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op (M.op X1 X0) X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75784 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq75784
    | (have j0 := eq75784 X0 X1
       grind)
    | exact resolve eq75784 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75784
  have eq75786 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75785 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75785
    | (have j0 := eq75785 X0 X1
       grind)
    | exact resolve eq75785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75785
  have eq76154 : x = y ∨ x = (k y y) ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq70967
       have i₂ := eq70973
       grind)
    | exact superpose eq70973 eq70967
    | exact resolve eq70967 eq70973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70967 eq70973
  have eq76171 : x = (k y y) ∨ x = y := by grind
  clear eq76154
  have eq77724 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq77725 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77724 X0 X1
       have j1 := eq298 X1 X0
       grind)
    | (have r₁ := eq77724 (k X1 X1) X0
       have r₂ := eq298 X0 X1
       grind)
    | (have r₁ := eq77724 X0 (σ (k X1 X1))
       have r₂ := eq298 (σ X0) X1
       grind)
    | (have r₁ := eq77724 X1 X0
       have r₂ := eq298 X0 X1
       grind)
    | exact resolve eq77724 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq77724
  have eq77763 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq77725 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq77725 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq77725 eq16
    | (have j1 := eq77725 (τ X1) X0
       grind)
    | exact resolve eq16 eq77725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq77764 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq77725 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq77725 X0 (σ X0)
       grind)
    | exact superpose eq77725 eq9
    | (have j1 := eq77725 X1 X0
       grind)
    | exact resolve eq9 eq77725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77725
  have eq77788 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq77763 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq77763
    | (have j0 := eq77763 X0 X1
       grind)
    | exact resolve eq77763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77763
  have eq77794 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq77788 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77788
    | (have j0 := eq77788 X0 X1
       grind)
    | exact resolve eq77788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77788
  have eq78535 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X0)) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq77764 (σ X0) X1
       grind)
    | exact superpose eq77764 eq13
    | (have j1 := eq77764 (σ X0) X1
       grind)
    | exact resolve eq13 eq77764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77764
  have eq78543 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78535 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq78535
    | (have j0 := eq78535 X0 X1
       grind)
    | exact resolve eq78535 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78535
  have eq79380 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq78543 x y
       grind)
    | exact superpose eq78543 eq14
    | (have j1 := eq78543 x y
       grind)
    | exact resolve eq14 eq78543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79400 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq79380
       have i₂ := eq11859
       grind)
    | exact superpose eq11859 eq79380
    | exact resolve eq79380 eq11859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11859 eq79380
  have eq79428 : (σ y) ≠ (σ y) ∨ x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79400
       have i₂ := eq12265
       grind)
    | exact superpose eq12265 eq79400
    | (have r₁ := eq79400
       have r₂ := eq12265
       grind)
    | exact resolve eq79400 eq12265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265 eq79400
  have eq79429 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq79428
  have eq79534 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq79429
       grind)
    | exact superpose eq79429 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq79429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79429
  have eq79572 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq79534
  have eq80107 : x ≠ y ∨ x = (M.op y y) := by grind
  clear eq79572
  have eq80130 : x = (M.op y y) := by
    first
    | (have r₁ := eq80107
       have r₂ := eq70730
       grind)
    | exact resolve eq80107 eq70730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70730 eq80107
  have eq80301 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq8 y y
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq8
    | exact resolve eq8 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80311 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq61
    | exact resolve eq61 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq80469 : x ≠ y ∨ y = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq58255 y y
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq58255
    | (have j0 := eq58255 y y
       grind)
    | exact resolve eq58255 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58255
  have eq80477 : y = (k y y) ∨ x = (k y y) := by
    first
    | (have r₁ := eq80469
       have r₂ := eq76171
       grind)
    | exact resolve eq80469 eq76171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80469
  have eq82213 : x ≠ y ∨ x = (k y y) := by grind
  clear eq80477
  have eq82243 : x = (k y y) := by
    first
    | (have r₁ := eq82213
       have r₂ := eq76171
       grind)
    | exact resolve eq82213 eq76171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76171 eq82213
  have eq82388 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq77794 X0 y
       have i₂ := eq82243
       grind)
    | exact superpose eq82243 eq77794
    | (have j0 := eq77794 X0 y
       grind)
    | exact resolve eq77794 eq82243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82243
  have eq82589 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = x := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq82388 (τ X0)
       grind)
    | exact superpose eq82388 eq17
    | (have j1 := eq82388 (τ X0)
       grind)
    | exact resolve eq17 eq82388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq82388
  have eq97164 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq82589 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq82589
    | exact resolve eq82589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82589
  have eq97185 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq97164 X0
       have i₂ := eq13 y X0
       grind)
    | exact superpose eq13 eq97164
    | (have j0 := eq97164 X0
       grind)
    | exact resolve eq97164 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97164
  have eq104969 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq75786 X0 x
       have i₂ := eq12167 X0 x
       grind)
    | exact superpose eq12167 eq75786
    | (have j0 := eq75786 X0 x
       have j1 := eq12167 X0 x
       grind)
    | exact resolve eq75786 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12167 eq75786
  have eq105001 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104969 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104969
  have eq105019 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105001 X0
       have j1 := eq77794 X0 X0
       grind)
    | (have r₁ := eq105001 X0
       have r₂ := eq77794 X0 X0
       grind)
    | (have r₁ := eq105001 (k x x)
       have r₂ := eq77794 (k (k x x) (k x x)) x
       grind)
    | exact resolve eq105001 eq77794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77794 eq105001
  have eq105252 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq105019 (σ X0)
       grind)
    | exact superpose eq105019 eq13
    | exact resolve eq13 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105252 X0
       have i₂ := eq105019 X0
       grind)
    | exact superpose eq105019 eq105252
    | exact resolve eq105252 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105252
  have eq105850 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq105332 X0
       grind)
    | exact superpose eq105332 eq8
    | exact resolve eq8 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105898 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (σ X0) (σ X0)
       have i₂ := eq105332 X0
       grind)
    | exact superpose eq105332 eq18
    | exact resolve eq18 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108231 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq105850 y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq105850
    | exact resolve eq105850 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105850
  have eq108520 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) ∨ (k y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq108231 (σ X0)
       have i₂ := eq78543 X0 y
       grind)
    | exact superpose eq78543 eq108231
    | (have j1 := eq78543 X0 y
       grind)
    | exact resolve eq108231 eq78543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108910 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq108520 X0
       have i₂ := eq105019 y
       grind)
    | exact superpose eq105019 eq108520
    | (have j0 := eq108520 X0
       grind)
    | exact resolve eq108520 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108520
  have eq109023 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (k y X0)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq108910 X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq108910
    | (have j0 := eq108910 X0
       grind)
    | exact resolve eq108910 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108910
  have eq109176 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq105898 y X0
       have i₂ := eq80130
       grind)
    | exact superpose eq80130 eq105898
    | exact resolve eq105898 eq80130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80130 eq105898
  have eq109626 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq108231 x
       have i₂ := eq109176 x
       grind)
    | exact superpose eq109176 eq108231
    | exact resolve eq108231 eq109176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108231 eq109176
  have eq110255 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq352 y x
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq352
    | (have j0 := eq352 y x
       grind)
    | exact resolve eq352 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq110260 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq78543 y x
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq78543
    | (have j0 := eq78543 y x
       grind)
    | exact resolve eq78543 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78543
  have eq110320 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110260
       have i₂ := eq105019 x
       grind)
    | exact superpose eq105019 eq110260
    | exact resolve eq110260 eq105019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105019 eq110260
  have eq113771 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110255
       grind)
    | exact superpose eq110255 eq14
    | exact resolve eq14 eq110255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110255
  have eq113824 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq113771
       have i₂ := eq1475 y x
       grind)
    | exact superpose eq1475 eq113771
    | (have j1 := eq1475 y x
       grind)
    | exact resolve eq113771 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq113771
  have eq113826 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = (k x y) := by grind
  clear eq113824
  have eq113827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq113826
       have i₂ := eq80301
       grind)
    | exact superpose eq80301 eq113826
    | exact resolve eq113826 eq80301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113826
  have eq113828 : x = (k x y) := by grind
  clear eq113827
  have eq113872 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1223 y x
       have i₂ := eq113828
       grind)
    | exact superpose eq113828 eq1223
    | (have j0 := eq1223 y x
       grind)
    | exact resolve eq1223 eq113828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq113906 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113872
       have i₂ := eq80301
       grind)
    | exact superpose eq80301 eq113872
    | exact resolve eq113872 eq80301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80301 eq113872
  have eq116340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq110320
       grind)
    | exact superpose eq110320 eq14
    | exact resolve eq14 eq110320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110320
  have eq116369 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116340
       have i₂ := eq113828
       grind)
    | exact superpose eq113828 eq116340
    | exact resolve eq116340 eq113828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113828 eq116340
  have eq116377 : y = (M.op x x) := by
    first
    | (have r₁ := eq116369
       have r₂ := eq113906
       grind)
    | exact resolve eq116369 eq113906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113906 eq116369
  have eq116419 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq19
    | exact resolve eq19 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116543 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq19 x x
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq19
    | exact resolve eq19 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq118947 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq80311 X0
       have i₂ := eq116419 X0
       grind)
    | exact superpose eq116419 eq80311
    | exact resolve eq80311 eq116419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116419
  have eq131575 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq109023 X0
       have i₂ := eq97185 X0
       grind)
    | exact superpose eq97185 eq109023
    | (have j0 := eq109023 X0
       have j1 := eq97185 X0
       grind)
    | exact resolve eq109023 eq97185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97185 eq109023
  have eq131582 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq131575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131575
  have eq131591 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op X0 y)) (σ X0)) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq131582 X0
       have i₂ := eq109626
       grind)
    | exact superpose eq109626 eq131582
    | (have j0 := eq131582 X0
       grind)
    | exact resolve eq131582 eq109626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109626 eq131582
  have eq136182 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131591 (M.op x y)
       have i₂ := eq116543
       grind)
    | exact superpose eq116543 eq131591
    | (have j0 := eq131591 (M.op x y)
       grind)
    | exact resolve eq131591 eq116543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116543 eq131591
  have eq136198 : (M.op (σ x) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136182
       have i₂ := eq105332 (M.op x y)
       grind)
    | exact superpose eq105332 eq136182
    | exact resolve eq136182 eq105332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136182
  have eq136199 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136198
       have i₂ := eq80311 x
       grind)
    | exact superpose eq80311 eq136198
    | exact resolve eq136198 eq80311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80311 eq136198
  have eq136200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136199
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq136199
    | exact resolve eq136199 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136199
  have eq136201 : x = (M.op x y) := by
    first
    | (have r₁ := eq136200
       have r₂ := eq14
       grind)
    | exact resolve eq136200 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136200
  have eq136352 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq118947 x
       have i₂ := eq136201
       grind)
    | exact superpose eq136201 eq118947
    | exact resolve eq118947 eq136201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118947
  have eq136686 : y = (M.op x y) := by
    first
    | (have i₁ := eq136352
       have i₂ := eq116377
       grind)
    | exact superpose eq116377 eq136352
    | exact resolve eq136352 eq116377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116377 eq136352
  have eq136848 : x = y := by
    first
    | (have i₁ := eq136686
       have i₂ := eq136201
       grind)
    | exact superpose eq136201 eq136686
    | exact resolve eq136686 eq136201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136201 eq136686
  have eq137233 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq136848
       grind)
    | exact superpose eq136848 eq14
    | exact resolve eq14 eq136848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136848
  have eq137712 : False := by grind
  exact eq137712
