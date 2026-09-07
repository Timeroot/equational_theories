import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4517`: `x ◇ (y ◇ z) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4517 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4517 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4517.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq17 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 X1)) X5) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 X0 (M.op X4 X1) X5
       have i₂ := eq8 X0 X4 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 (M.op X0 X2) X4 X5
       have i₂ := eq8 X0 X1 X2 X4
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq8 X0 x X1 X4
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq8 X0 X3 X2 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op x X2)
       have i₂ := eq8 (M.op X0 X1) x X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq36 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X0 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq41 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq78 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30
    | exact resolve eq30 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq106 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X3 X4 X5 (M.op X0 X1)
       have i₂ := eq19 X0 X1 X5 X2
       grind)
    | (have i₁ := eq23 X3 X4 X5 (M.op X0 X1)
       have i₂ := eq19 X0 X1 X2 X5
       grind)
    | exact superpose eq19 eq23
    | exact resolve eq23 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq153 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq41 X1 (τ X0) X2
       grind)
    | exact superpose eq41 eq15
    | (have j1 := eq41 X1 X1 X2
       grind)
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq157 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq41 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq41 eq13
    | (have j1 := eq41 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq163 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153
    | (have j0 := eq153 X0 X1 X2
       grind)
    | exact resolve eq153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq209 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 x x x X0 X1 X2
       have i₂ := eq18 x x x X0 X3 X4
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op X6 X1)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op x X3) X6
       have i₂ := eq24 (M.op (M.op X0 X1) X2) X3 X4 X5 x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq18 x x x (M.op (M.op X0 X2) X3) X4 X5
       have i₂ := eq24 X0 X2 X3 (M.op x (M.op x x)) X1
       grind)
    | exact superpose eq24 eq18
    | exact resolve eq18 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq483 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 X2)) ≠ (M.op X0 (M.op (M.op X1 X2) X3)) ∨ (M.op X0 (M.op X4 X2)) = (k (M.op X0 (M.op X4 X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq162 (M.op X0 (M.op X4 X2)) X5
       have i₂ := eq17 X1 X2 X3 X0 X4 X5
       grind)
    | exact superpose eq17 eq162
    | (have j0 := eq162 (M.op X0 (M.op X4 X2)) X5
       grind)
    | (have r₁ := eq162 (M.op X3 (M.op (M.op X0 X2) X2)) X5
       have r₂ := eq17 X0 X2 X2 X3 (M.op X0 X2) X5
       grind)
    | exact resolve eq162 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq162
  have eq517 : ∀ X0 X2 X4 X5 : G, (M.op X0 (M.op X4 X2)) = (k (M.op X0 (M.op X4 X2)) X5) := by
    intro X0 X2 X4 X5
    first
    | (have j0 := eq483 X0 x X2 x X4 X5
       grind)
    | (have r₁ := eq483 x x X2 X5 (M.op X0 x) X5
       have r₂ := eq106 X0 x X2 x (M.op x X2) X5
       grind)
    | (have r₁ := eq483 x X0 x X2 X4 X5
       have r₂ := eq106 X0 x X2 x X4 x
       grind)
    | exact resolve eq483 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq483
  have eq1306 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = X0 ∨ (k X2 X0) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq36 X1 X1 X2 X3
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq36
    | (have j0 := eq36 X0 X1 X2 X2
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1567 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X3 X4 x
       have i₂ := eq209 X0 X4 x X1 X2
       grind)
    | (have i₁ := eq8 X0 X3 X4 x
       have i₂ := eq209 X0 X1 X2 X4 x
       grind)
    | exact superpose eq209 eq8
    | exact resolve eq8 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq1788 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq1567 X0 X2 x X3 X4
       grind)
    | exact superpose eq1567 eq8
    | exact resolve eq8 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1935 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq39 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq11 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1975 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (σ X0) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 (σ X1) (σ X1) X2 x
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq19
    | (have j1 := eq39 X3 X0
       grind)
    | exact resolve eq19 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq2005 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1935 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1935 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1935 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq6652 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2005 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2005
    | (have j0 := eq2005 (τ X0) X1
       grind)
    | exact resolve eq2005 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq6669 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6652 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6652
    | (have j0 := eq6652 X0 X1
       grind)
    | exact resolve eq6652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6652
  have eq6678 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6669 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6669
    | (have j0 := eq6669 X0 X1
       grind)
    | exact resolve eq6669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6669
  have eq7125 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6678 (τ X0) X1
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq6678
    | (have j0 := eq6678 (τ X0) X1
       grind)
    | exact resolve eq6678 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6678
  have eq7493 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq7721 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7493 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq7493
    | (have j0 := eq7493 X0 X1
       grind)
    | exact resolve eq7493 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7493
  have eq15678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2000 X0
       have i₂ := eq163 X1 X0 X0
       grind)
    | exact superpose eq163 eq2000
    | (have j0 := eq2000 X0
       have j1 := eq163 X1 X0 x
       grind)
    | exact resolve eq2000 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq15712 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2000 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq2000
    | (have j0 := eq2000 (τ X0)
       grind)
    | exact resolve eq2000 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq15741 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq15712 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15712
    | (have j0 := eq15712 X0
       grind)
    | exact resolve eq15712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15712
  have eq15754 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15678 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq15678 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq15678 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15678
  have eq15755 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15741 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15741
    | (have j0 := eq15741 X0
       grind)
    | exact resolve eq15741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15741
  have eq17033 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = X1 ∨ (σ (M.op X2 X0)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15754 X0 X1
       have i₂ := eq7721 X2 X0
       grind)
    | exact superpose eq7721 eq15754
    | (have j0 := eq15754 X0 X1
       have j1 := eq7721 X2 X0
       grind)
    | exact resolve eq15754 eq7721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7721 eq15754
  have eq17246 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = X1 ∨ (σ (M.op X2 X0)) = (σ (k X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17033 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17033
  have eq17309 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq157 x y X0
       grind)
    | exact superpose eq157 eq14
    | (have j1 := eq157 X0 y X0
       grind)
    | exact resolve eq14 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq17447 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq17309 X0
       have j1 := eq17246 y X0 x
       grind)
    | (have r₁ := eq17309 X0
       have r₂ := eq17246 y x x
       grind)
    | exact resolve eq17309 eq17246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17246 eq17309
  have eq17478 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15755 (σ y)
       have i₂ := eq17447 (σ y)
       grind)
    | exact superpose eq17447 eq15755
    | (have j0 := eq15755 (σ y)
       grind)
    | (have r₁ := eq15755 (σ y)
       have r₂ := eq17447 (σ y)
       grind)
    | exact resolve eq15755 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17480 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7125 (σ y) X0
       have i₂ := eq17447 (σ y)
       grind)
    | exact superpose eq17447 eq7125
    | (have j0 := eq7125 (σ y) X0
       grind)
    | exact resolve eq7125 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7125 eq17447
  have eq17504 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq17480 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq17506 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17478
  have eq17512 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq17504 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17504
    | exact resolve eq17504 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17504
  have eq17706 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15755 y
       have i₂ := eq17512 y
       grind)
    | exact superpose eq17512 eq15755
    | (have j0 := eq15755 y
       grind)
    | (have r₁ := eq15755 y
       have r₂ := eq17512 y
       grind)
    | exact resolve eq15755 eq17512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15755 eq17512
  have eq17731 : y = (M.op y y) := by grind
  clear eq17706
  have eq18506 : ∀ X0 X1 : G, (M.op y X1) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 y y x x
       have i₂ := eq17731
       grind)
    | exact superpose eq17731 eq19
    | exact resolve eq19 eq17731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq18569 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1788 X0 X1 X2 y y
       have i₂ := eq17731
       grind)
    | exact superpose eq17731 eq1788
    | exact resolve eq1788 eq17731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20097 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) X6) X7) X8) X9) = (M.op X0 (M.op X10 X1)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10
    first
    | (have i₁ := eq311 X0 X1 X2 X3 X4 (M.op x X5) X10
       have i₂ := eq311 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5 X6 X7 X8 X9 x
       grind)
    | exact superpose eq311 eq311
    | exact resolve eq311 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20544 : ∀ X0 X1 X2 X3 X4 X5 X7 X8 X9 X10 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) X7) X8) X9) X10) := by
    intro X0 X1 X2 X3 X4 X5 X7 X8 X9 X10
    first
    | (have i₁ := eq354 (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) x X7 X8 X9 X10
       have i₂ := eq311 X0 X2 X3 X4 X5 (M.op x X7) X1
       grind)
    | exact superpose eq311 eq354
    | exact resolve eq354 eq311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311 eq354
  have eq20579 : ∀ X0 X2 X3 X4 X5 X7 X8 X9 X10 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X3) X4) X5) X7) X8) X9) X10) := by
    intro X0 X2 X3 X4 X5 X7 X8 X9 X10
    first
    | (have i₁ := eq20544 X0 x X2 X3 X4 X5 X7 X8 X9 X10
       have i₂ := eq18569 X0 x X2
       grind)
    | exact superpose eq18569 eq20544
    | exact resolve eq20544 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20544
  have eq20614 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op X0 y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) X6) X7) X8) X9) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq20097 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 x
       have i₂ := eq18569 X0 x X1
       grind)
    | exact superpose eq18569 eq20097
    | exact resolve eq20097 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20097
  have eq20648 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq20614 X0 X1 x x x x x x x x
       have i₂ := eq20579 (M.op X0 X1) x x x x x x x x
       grind)
    | exact superpose eq20579 eq20614
    | exact resolve eq20614 eq20579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20579 eq20614
  have eq24222 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq17731
       have i₂ := eq18506 X0 y
       grind)
    | (have i₁ := eq17731
       have i₂ := eq18506 y X0
       grind)
    | exact superpose eq18506 eq17731
    | exact resolve eq17731 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17731 eq18506
  have eq25646 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 y x x X0 X1 X2
       have i₂ := eq24222 (M.op x x)
       grind)
    | exact superpose eq24222 eq18
    | exact resolve eq18 eq24222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24222
  have eq30555 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1788 X0 X1 X2 (σ y) (σ y)
       have i₂ := eq17506
       grind)
    | exact superpose eq17506 eq1788
    | exact resolve eq1788 eq17506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq17506
  have eq30568 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq30555 X0 x x
       have i₂ := eq18569 X0 x x
       grind)
    | exact superpose eq18569 eq30555
    | exact resolve eq30555 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30555
  have eq34173 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30568 (σ x)
       grind)
    | exact superpose eq30568 eq14
    | exact resolve eq14 eq30568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30568
  have eq52143 : ∀ X0 X3 X4 X5 : G, (k X0 X3) = X0 ∨ (M.op X4 X0) = (k X4 X0) ∨ (k X5 X0) = (M.op X5 X0) := by
    intro X0 X3 X4 X5
    first
    | (have i₁ := eq517 X0 x X4 X5
       have i₂ := eq1306 X0 (M.op X4 x) x X3
       grind)
    | exact superpose eq1306 eq517
    | (have j1 := eq1306 X0 x X4 X4
       grind)
    | exact resolve eq517 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq52486 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1306 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq52487 : ∀ X0 X1 X2 : G, (M.op X1 X2) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq52486 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52486
  have eq55450 : ∀ X0 X1 : G, (M.op (σ X0) X1) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1975 X0 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq348611 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq55450 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55450
    | exact resolve eq55450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55450
  have eq348964 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq348611 X0 X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq348611
    | (have j0 := eq348611 X0 X1
       grind)
    | exact resolve eq348611 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348611
  have eq348968 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq348964 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq348964
    | (have j0 := eq348964 X0 X1
       grind)
    | exact resolve eq348964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348964
  have eq348971 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X1) ≠ (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq348968 X0 X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq348968
    | (have j0 := eq348968 X0 X1
       grind)
    | exact resolve eq348968 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq348968
  have eq348972 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq348971 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq348971
    | (have j0 := eq348971 X0 X1
       grind)
    | exact resolve eq348971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348971
  have eq355563 : ∀ X0 X2 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq348972 X0 x
       have i₂ := eq52487 X2 X0 x
       grind)
    | exact superpose eq52487 eq348972
    | (have j0 := eq348972 X0 x
       have j1 := eq52487 X0 X0 X2
       grind)
    | (have r₁ := eq348972 x x
       have r₂ := eq52487 x x X2
       grind)
    | exact resolve eq348972 eq52487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52487 eq348972
  have eq355673 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X2
    first
    | (have j0 := eq355563 X0 X0
       have j1 := eq52143 X0 x X0 X0
       grind)
    | (have r₁ := eq355563 x X2
       have r₂ := eq52143 x x x x
       grind)
    | exact resolve eq355563 eq52143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52143 eq355563
  have eq385693 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq355673 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355673
  have eq385694 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq385693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385693
  have eq386121 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0 X0
       have i₂ := eq385694 (τ X0)
       grind)
    | exact superpose eq385694 eq78
    | exact resolve eq78 eq385694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq386138 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq386121 X0
       have i₂ := eq385694 X0
       grind)
    | exact superpose eq385694 eq386121
    | exact resolve eq386121 eq385694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385694 eq386121
  have eq387136 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18569 X1 (τ X0) (τ X0)
       have i₂ := eq386138 X0
       grind)
    | exact superpose eq386138 eq18569
    | exact resolve eq18569 eq386138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387141 : ∀ X0 X1 : G, (M.op (τ X0) y) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25646 (τ X0) (τ X0) X1
       have i₂ := eq386138 X0
       grind)
    | exact superpose eq386138 eq25646
    | exact resolve eq25646 eq386138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25646
  have eq390352 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) y) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq386138 (M.op X0 X0)
       have i₂ := eq387136 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq387136 eq386138
    | exact resolve eq386138 eq387136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386138 eq387136
  have eq390417 : ∀ X0 : G, (τ (M.op (M.op X0 X0) y)) = (M.op (τ (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq390352 X0
       have i₂ := eq18569 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq18569 eq390352
    | exact resolve eq390352 eq18569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18569 eq390352
  have eq390582 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op (M.op X0 X0) y)) := by
    intro X0
    first
    | (have i₁ := eq390417 X0
       have i₂ := eq387141 X0 y
       grind)
    | exact superpose eq387141 eq390417
    | exact resolve eq390417 eq387141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387141 eq390417
  have eq390601 : ∀ X0 : G, (M.op (τ X0) y) = (τ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq390582 X0
       have i₂ := eq20648 X0 X0
       grind)
    | exact superpose eq20648 eq390582
    | exact resolve eq390582 eq20648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20648 eq390582
  have eq390819 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 y)
       have i₂ := eq390601 X0
       grind)
    | exact superpose eq390601 eq10
    | exact resolve eq10 eq390601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390601
  have eq391153 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq390819 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq390819
    | exact resolve eq390819 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390819
  have eq391576 : (M.op (σ x) y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq34173
       have i₂ := eq391153 x
       grind)
    | exact superpose eq391153 eq34173
    | (have r₁ := eq34173
       have r₂ := eq391153 x
       grind)
    | exact resolve eq34173 eq391153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34173 eq391153
  have eq391605 : False := by grind
  exact eq391605

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation452 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq96 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq96 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq96 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq116 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq13
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq116
    | exact resolve eq116 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq116
  have eq1160 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq123 x y
       grind)
    | exact superpose eq123 eq14
    | (have r₁ := eq14
       have r₂ := eq123 x y
       grind)
    | exact resolve eq14 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq1183 : False := by grind
  exact eq1183

/-- `Equation4535`: `x ◇ (y ◇ z) = (y ◇ w) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4535 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4535 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4535.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X3) X0) := by
    intro X0 X1 X2 X3
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq18 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X3) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 x) X5
       have i₂ := eq8 X2 X0 x X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X3) X0 X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X4) X5) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 X3 (M.op X1 X4) X0 X5
       have i₂ := eq8 X0 X1 X2 X4
       grind)
    | (have i₁ := eq8 X0 X0 (M.op X1 X2) X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X2 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X3 X2 X4 (M.op X0 x)
       have i₂ := eq8 X2 X0 x X1
       grind)
    | (have i₁ := eq8 X0 (M.op X1 X3) X2 X0
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 X2 x
       have i₂ := eq8 X0 X1 X3 x
       grind)
    | (have i₁ := eq8 (M.op X1 X2) X1 X2 X3
       have i₂ := eq8 (M.op X1 X3) X1 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X4) (M.op X2 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8 (M.op X0 X1) X2 X3 X5
       have i₂ := eq8 (M.op X2 X5) X0 X1 X4
       grind)
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq38 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X3)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X1 X3)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X3) X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X2 X3
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2 X3
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq46 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq12 X0 (τ X1)
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq17 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq86 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32
    | exact resolve eq32 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op X3 (M.op X2 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X2 X4 (M.op X0 x)
       have i₂ := eq8 X2 X0 x X1
       grind)
    | (have i₁ := eq24 X0 (M.op X1 X3) X2 X0
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq24
    | exact resolve eq24 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq33 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq187 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq173
    | exact resolve eq173 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq251 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op (M.op X3 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X2 (M.op X3 X4) X0 X5
       have i₂ := eq18 X3 X4 X0 X2 X1
       grind)
    | (have i₁ := eq24 (M.op X2 X5) X1 X2 X3
       have i₂ := eq18 X0 X1 X2 (M.op X1 X2) X5
       grind)
    | exact superpose eq18 eq24
    | exact resolve eq24 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq272 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X3) ∨ (M.op X1 X3) = (k (M.op X1 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq165 (M.op X1 X3) X0
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | (have i₁ := eq165 X0 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2 X3
       grind)
    | exact superpose eq8 eq165
    | (have j0 := eq165 (M.op X1 X3) X0
       grind)
    | (have r₁ := eq165 (M.op X0 (M.op X0 X2)) X0
       have r₂ := eq8 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact resolve eq165 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X3 X4) X2) X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X3 X4 X2 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq22 X0 X1 X2 X3 X4
       have i₂ := eq12 X0 (M.op X2 X4)
       grind)
    | exact superpose eq12 eq22
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq187 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq187
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X5) X0) = (M.op (M.op X1 X2) (M.op X3 X4)) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 X1 X2 X3 X4 X5 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq25 X0 X1 X2 X3 X4 X5
       have i₂ := eq12 X0 (M.op X2 X5)
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq1477 : ∀ X0 X1 X2 X5 X6 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X5 X6)) := by
    intro X0 X1 X2 X5 X6
    first
    | (have i₁ := eq111 x x X5 X2 X6
       have i₂ := eq251 X0 X1 X2 x x X5
       grind)
    | (have i₁ := eq111 X0 X1 X2 (M.op X0 X1) x
       have i₂ := eq251 X0 X1 (M.op (M.op X0 X1) X2) x x X5
       grind)
    | exact superpose eq251 eq111
    | exact resolve eq111 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1479 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq18 x x X0 X2 X1
       have i₂ := eq251 X3 X4 X2 x x X0
       grind)
    | (have i₁ := eq18 X0 X1 X2 (M.op X0 X1) x
       have i₂ := eq251 X0 X1 (M.op (M.op X0 X1) X2) X3 X4 x
       grind)
    | exact superpose eq251 eq18
    | exact resolve eq18 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq251
  have eq1700 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X4 X5) (M.op X6 X7)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq1477 X0 X1 (M.op X2 X3) X4 X5
       have i₂ := eq1477 X2 X3 (M.op X4 X5) X6 X7
       grind)
    | (have i₁ := eq1477 X0 X1 X2 X5 X6
       have i₂ := eq1477 X0 X1 X2 X5 X6
       grind)
    | exact superpose eq1477 eq1477
    | exact resolve eq1477 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1720 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 x x X1 X0 X2
       have i₂ := eq1477 (M.op x x) X1 X0 X3 X4
       grind)
    | (have i₁ := eq22 X0 X1 X2 (M.op x x) X4
       have i₂ := eq1477 X0 X1 (M.op (M.op X0 X1) X2) x x
       grind)
    | exact superpose eq1477 eq22
    | exact resolve eq22 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1727 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    grind
  have eq1900 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X4 X5) ∨ (M.op X0 X4) = (k X0 X4) ∨ (M.op X2 X5) = (k X2 X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq39 X4 X5 X0 X1
       have i₂ := eq39 X5 (M.op X0 X1) X2 X3
       grind)
    | (have i₁ := eq39 X0 X1 X2 X3
       have i₂ := eq39 X0 X1 X2 X3
       grind)
    | exact superpose eq39 eq39
    | (have j0 := eq39 X4 X1 X0 X3
       have j1 := eq39 X4 X1 X0 X3
       grind)
    | exact resolve eq39 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1999 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X3) X4) X1) ∨ (M.op X5 X0) = (k X5 X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19 X5 X2 x X1 X3 X4
       have i₂ := eq39 X0 X1 X5 (M.op X2 x)
       grind)
    | (have i₁ := eq19 X0 X1 X2 X0 X4 X5
       have i₂ := eq39 X0 (M.op X0 (M.op X1 X2)) X2 X3
       grind)
    | exact superpose eq39 eq19
    | (have j1 := eq39 X0 X1 X5 X3
       grind)
    | exact resolve eq19 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq39
  have eq2458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k X2 X3) = X2 ∨ (M.op X0 X3) = (k X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq165 X2 X3
       have i₂ := eq40 X3 X2 X0 X1
       grind)
    | (have i₁ := eq165 (M.op X2 X3) X1
       have i₂ := eq40 X0 X1 X2 X3
       grind)
    | exact superpose eq40 eq165
    | (have j0 := eq165 X2 X3
       have j1 := eq40 X3 X1 X0 X3
       grind)
    | (have r₁ := eq165 (M.op X1 X0) X1
       have r₂ := eq40 X0 X1 X1 X0
       grind)
    | exact resolve eq165 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2847 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) ≠ X0 ∨ (k X0 (M.op X3 X4)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq165 X0 (M.op X3 X4)
       have i₂ := eq1720 X0 X3 X4 X1 X2
       grind)
    | (have i₁ := eq165 X0 (M.op X3 X4)
       have i₂ := eq1720 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq1720 eq165
    | (have j0 := eq165 X0 (M.op X1 X2)
       grind)
    | exact resolve eq165 eq1720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3265 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq43 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq43
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3281 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq14
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3326 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq9
    | (have j1 := eq43 X0 X1
       grind)
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3380 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq12811 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3380 (τ X0)
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq3380
    | (have j0 := eq3380 (τ X0)
       grind)
    | exact resolve eq3380 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12813 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12811 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12811
    | (have j0 := eq12811 X0
       grind)
    | exact resolve eq12811 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12811
  have eq12816 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12813 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12813
    | (have j0 := eq12813 X0
       grind)
    | exact resolve eq12813 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12813
  have eq12829 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12816 (τ X0)
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq12816
    | (have j0 := eq12816 (τ X0)
       grind)
    | exact resolve eq12816 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12816
  have eq12935 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq46
    | exact resolve eq46 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13151 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq10
    | (have j1 := eq46 X0 X1
       grind)
    | exact resolve eq10 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13153 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (σ (k X1 (M.op X0 X0))) ∨ (k (σ X0) X2) = (σ (M.op X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X2 X1
       have i₂ := eq46 X0 X2
       grind)
    | exact superpose eq46 eq17
    | (have j1 := eq46 X0 X2
       grind)
    | exact resolve eq17 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq46
  have eq13179 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12935 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq12935
    | (have j0 := eq12935 X0 X1
       grind)
    | exact resolve eq12935 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12935
  have eq15867 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq158 x y
       grind)
    | exact superpose eq158 eq14
    | (have j1 := eq158 x y
       grind)
    | exact resolve eq14 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15873 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq158 X0 X0
       grind)
    | exact superpose eq158 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq158 X0 X0
       grind)
    | exact resolve eq12 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq16578 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq145
    | (have j0 := eq145 X1 (σ X0)
       grind)
    | exact resolve eq145 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq16643 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16578 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq16578
    | (have j0 := eq16578 X0 X1
       grind)
    | exact resolve eq16578 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16578
  have eq18602 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3380 X0
       have i₂ := eq16643 X0 X0
       grind)
    | exact superpose eq16643 eq3380
    | (have j0 := eq3380 X0
       have j1 := eq16643 X0 X0
       grind)
    | (have r₁ := eq3380 x
       have r₂ := eq16643 x x
       grind)
    | exact resolve eq3380 eq16643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16643
  have eq18629 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602
  have eq28423 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq514
    | (have j0 := eq514 X1 (τ X0)
       grind)
    | exact resolve eq514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28471 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq514 (σ X1) X0
       grind)
    | exact superpose eq514 eq32
    | (have j1 := eq514 (σ X1) X0
       grind)
    | exact resolve eq32 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq28499 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28471 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq28471
    | (have j0 := eq28471 X0 X1
       grind)
    | exact resolve eq28471 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28471
  have eq28519 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28423 X0 X1
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq28423
    | (have j0 := eq28423 X0 X1
       grind)
    | exact resolve eq28423 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28423
  have eq28532 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28499 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq28499
    | (have j0 := eq28499 X0 X1
       grind)
    | exact resolve eq28499 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28499
  have eq32143 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 X5) = (k (M.op X4 X5) (M.op (M.op X0 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    grind
  clear eq1700
  have eq37419 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3281
       have i₂ := eq13179 y x
       grind)
    | exact superpose eq13179 eq3281
    | (have j1 := eq13179 (σ y) (σ x)
       grind)
    | (have r₁ := eq3281
       have r₂ := eq13179 y x
       grind)
    | exact resolve eq3281 eq13179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37420 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq37419
  have eq37431 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq37420
       grind)
    | exact superpose eq37420 eq187
    | exact resolve eq187 eq37420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37585 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq37431
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq37431
    | exact resolve eq37431 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37431
  have eq37693 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq37585
       grind)
    | exact superpose eq37585 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq37585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37696 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13179 y x
       have i₂ := eq37585
       grind)
    | exact superpose eq37585 eq13179
    | (have j0 := eq13179 y x
       grind)
    | exact resolve eq13179 eq37585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13179 eq37585
  have eq37697 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq37696
  have eq37698 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq37693
  have eq39005 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1477 x y X0 X1 X2
       have i₂ := eq37698
       grind)
    | exact superpose eq37698 eq1477
    | exact resolve eq1477 eq37698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39017 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1720 X0 X1 X2 x y
       have i₂ := eq37698
       grind)
    | exact superpose eq37698 eq1720
    | exact resolve eq1720 eq37698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45571 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3326 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3326
    | exact resolve eq3326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326
  have eq45806 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45571 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq45571
    | (have j0 := eq45571 X0 X1
       grind)
    | exact resolve eq45571 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45571
  have eq47704 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39005 X0 x y
       have i₂ := eq37698
       grind)
    | exact superpose eq37698 eq39005
    | exact resolve eq39005 eq37698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37698 eq39005
  have eq48189 : ∀ X0 : G, (M.op x X0) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq47704 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47704
  have eq50000 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq165 x X0
       have i₂ := eq48189 X0
       grind)
    | (have i₁ := eq165 X0 x
       have i₂ := eq48189 X0
       grind)
    | exact superpose eq48189 eq165
    | (have j0 := eq165 x X0
       grind)
    | exact resolve eq165 eq48189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48189
  have eq62405 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39017 X0 (σ x) (σ x)
       have i₂ := eq37420
       grind)
    | exact superpose eq37420 eq39017
    | exact resolve eq39017 eq37420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62983 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq62405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62405
  have eq64975 : (σ (M.op x y)) ≠ (M.op (σ x) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq62983 (σ x)
       grind)
    | exact superpose eq62983 eq14
    | exact resolve eq14 eq62983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62983
  have eq77712 : (σ x) ≠ (M.op (σ x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64975
       have i₂ := eq37697
       grind)
    | exact superpose eq37697 eq64975
    | exact resolve eq64975 eq37697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37697 eq64975
  have eq77713 : (σ x) ≠ (M.op (σ x) x) ∨ y = (M.op x x) := by grind
  clear eq77712
  have eq81428 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq45806 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45806
    | (have j0 := eq45806 X1 (τ X0)
       grind)
    | exact resolve eq45806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101483 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12829 X0
       have i₂ := eq28519 X0 X0
       grind)
    | exact superpose eq28519 eq12829
    | (have j0 := eq12829 X0
       have j1 := eq28519 X0 X0
       grind)
    | (have r₁ := eq12829 x
       have r₂ := eq28519 x x
       grind)
    | exact resolve eq12829 eq28519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28519
  have eq101489 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq101483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101483
  have eq116351 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28532 x x
       have i₂ := eq37420
       grind)
    | exact superpose eq37420 eq28532
    | (have j0 := eq28532 x x
       grind)
    | exact resolve eq28532 eq37420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28532 eq37420
  have eq116417 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116351
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq116351
    | exact resolve eq116351 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116351
  have eq202160 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq116417
       grind)
    | exact superpose eq116417 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq116417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116417
  have eq202188 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (k x x) := by grind
  clear eq202160
  have eq202203 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq50000 x
       grind)
    | (have r₁ := eq202188
       have r₂ := eq50000 x
       grind)
    | exact resolve eq202188 eq50000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50000 eq202188
  have eq207578 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3380 x
       have i₂ := eq202203
       grind)
    | exact superpose eq202203 eq3380
    | (have j0 := eq3380 x
       grind)
    | exact resolve eq3380 eq202203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202203
  have eq207605 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq207578
  have eq221981 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39017 X0 (σ x) (σ x)
       have i₂ := eq207605
       grind)
    | exact superpose eq207605 eq39017
    | exact resolve eq39017 eq207605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39017
  have eq221999 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq221981 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221981
  have eq229298 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (M.op (M.op X0 X2) (M.op X0 X3)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1900 X0 X2 X0 X3 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900
  have eq229299 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X0 X2) (M.op X0 X3)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq229298 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229298
  have eq274979 : (σ x) = (M.op (σ x) x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq207605
       have i₂ := eq221999 (σ x)
       grind)
    | exact superpose eq221999 eq207605
    | exact resolve eq207605 eq221999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207605 eq221999
  have eq275037 : (σ x) = (M.op (σ x) x) ∨ y = (M.op x x) := by grind
  clear eq274979
  have eq275066 : y = (M.op x x) := by
    first
    | (have r₁ := eq275037
       have r₂ := eq77713
       grind)
    | exact resolve eq275037 eq77713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77713 eq275037
  have eq279185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X0) X1) = (M.op y (M.op X2 X3)) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq924 X1 x x X2 X3 X0
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq924
    | (have j0 := eq924 X1 X1 X2 X2 x x
       grind)
    | exact resolve eq924 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq279246 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1477 x x X0 X1 X2
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq1477
    | exact resolve eq1477 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279247 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X2 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1477 X0 X1 X2 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq1477
    | exact resolve eq1477 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq279249 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1479 X0 X1 X2 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq1479
    | exact resolve eq1479 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq279264 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1720 X0 X1 X2 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq1720
    | exact resolve eq1720 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq279268 : ∀ X0 X1 : G, y = (k y (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1727 x x x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq1727
    | exact resolve eq1727 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq279332 : ∀ X0 X1 X2 : G, (M.op X0 y) ≠ X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2847 X0 x x X1 X2
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq2847
    | (have j0 := eq2847 X0 X1 X2 X1 X2
       grind)
    | exact resolve eq2847 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq279365 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32143 x x X2 X3 X0 X1
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq32143
    | exact resolve eq32143 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279367 : ∀ X0 X1 X2 X3 : G, y = (k y (M.op (M.op X0 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32143 X0 X1 X2 X3 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq32143
    | exact resolve eq32143 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32143
  have eq279388 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op y y) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq279185 X0 X1 X2 x
       have i₂ := eq279264 y X2 x
       grind)
    | exact superpose eq279264 eq279185
    | (have j0 := eq279185 X0 X1 X2 x
       grind)
    | exact resolve eq279185 eq279264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279185
  have eq279418 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) ∨ (M.op y X1) = (M.op y y) := by
    intro X1 X2
    first
    | (have i₁ := eq279388 x X1 X2
       have i₂ := eq279249 x x X1
       grind)
    | exact superpose eq279249 eq279388
    | (have j0 := eq279388 x X1 X2
       grind)
    | exact resolve eq279388 eq279249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279388
  have eq283037 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op y X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279246 X1 (σ X0) (σ X0)
       have i₂ := eq18629 X0
       grind)
    | exact superpose eq18629 eq279246
    | (have j1 := eq18629 X0
       grind)
    | exact resolve eq279246 eq18629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283043 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op y X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279246 X1 (τ X0) (τ X0)
       have i₂ := eq101489 X0
       grind)
    | exact superpose eq101489 eq279246
    | (have j1 := eq101489 X0
       grind)
    | exact resolve eq279246 eq101489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283061 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq279246 X0 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq279246
    | exact resolve eq279246 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290409 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X0 y) ∨ (k X4 X1) = (M.op X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq278 X1 X0 X4 x x
       have i₂ := eq279247 (M.op x x) X4 X0
       grind)
    | exact superpose eq279247 eq278
    | (have j0 := eq278 X1 X1 X4 x X4
       grind)
    | exact resolve eq278 eq279247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq290418 : ∀ X0 X1 X5 : G, (M.op X1 X0) = (M.op X0 y) ∨ (k X5 X1) = (M.op X5 X1) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq1999 X1 X0 x x x X5
       have i₂ := eq279247 (M.op x x) x X0
       grind)
    | exact superpose eq279247 eq1999
    | (have j0 := eq1999 X1 X1 x x x X5
       grind)
    | exact resolve eq1999 eq279247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999
  have eq298452 : ∀ X0 : G, y = (k y (M.op y (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq279268 (σ X0) (σ X0)
       have i₂ := eq18629 X0
       grind)
    | exact superpose eq18629 eq279268
    | (have j1 := eq18629 X0
       grind)
    | exact resolve eq279268 eq18629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298458 : ∀ X0 : G, y = (k y (M.op y (τ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq279268 (τ X0) (τ X0)
       have i₂ := eq101489 X0
       grind)
    | exact superpose eq101489 eq279268
    | (have j1 := eq101489 X0
       grind)
    | exact resolve eq279268 eq101489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279268
  have eq378881 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq279365 X0 X1 x x
       have i₂ := eq279264 y x x
       grind)
    | exact superpose eq279264 eq279365
    | exact resolve eq279365 eq279264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279365
  have eq381168 : (τ (M.op y y)) ≠ (τ (M.op y y)) ∨ (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by
    first
    | (have i₁ := eq12829 (M.op y y)
       have i₂ := eq378881 y y
       grind)
    | exact superpose eq378881 eq12829
    | (have j0 := eq12829 (M.op y y)
       grind)
    | exact resolve eq12829 eq378881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12829 eq378881
  have eq381188 : (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by grind
  clear eq381168
  have eq419919 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq13151 X0 X1
       grind)
    | exact superpose eq13151 eq9
    | (have j1 := eq13151 X0 X1
       grind)
    | exact resolve eq9 eq13151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419924 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq13151 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13151
  have eq419925 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq419924 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq419924
    | (have j0 := eq419924 X0
       grind)
    | exact resolve eq419924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419924
  have eq419930 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq419919 X0 X1
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq419919
    | (have j0 := eq419919 X0 X1
       grind)
    | exact resolve eq419919 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419919
  have eq420099 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq419925 X0
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq419925
    | (have j0 := eq419925 X0
       have j1 := eq38 X0 X0
       grind)
    | (have r₁ := eq419925 X0
       have r₂ := eq38 X0 X0
       grind)
    | exact resolve eq419925 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq420134 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq420099 X0
       have j1 := eq419925 X0
       grind)
    | (have r₁ := eq420099 X0
       have r₂ := eq419925 X0
       grind)
    | exact resolve eq420099 eq419925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420099
  have eq420511 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq420134 (σ X0)
       have i₂ := eq18629 X0
       grind)
    | exact superpose eq18629 eq420134
    | (have j0 := eq420134 (σ X0)
       have j1 := eq18629 X0
       grind)
    | (have r₁ := eq420134 (σ X0)
       have r₂ := eq18629 X0
       grind)
    | exact resolve eq420134 eq18629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420134
  have eq420538 : ∀ X0 : G, (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq420511 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420511
  have eq420539 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq420538 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq420538
    | (have j0 := eq420538 X0
       grind)
    | exact resolve eq420538 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420538
  have eq421181 : y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq420539 x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq420539
    | exact resolve eq420539 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420539
  have eq430999 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X0 x (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq431000 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq430999 x x
       have i₂ := eq279264 x x x
       grind)
    | exact superpose eq279264 eq430999
    | exact resolve eq430999 eq279264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430999
  have eq431076 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq431000 (M.op X0 X1)
       have i₂ := eq279249 X0 X1 y
       grind)
    | exact superpose eq279249 eq431000
    | exact resolve eq431000 eq279249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448378 : ∀ X0 X1 : G, y = (k y (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279367 X1 x X1 x
       have i₂ := eq229299 X1 X0 x x
       grind)
    | (have i₁ := eq279367 X0 X1 X0 X1
       have i₂ := eq229299 X0 (M.op X0 X1) x x
       grind)
    | exact superpose eq229299 eq279367
    | (have j1 := eq229299 X1 X0 x x
       grind)
    | exact resolve eq279367 eq229299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279367
  have eq448559 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op y (M.op X1 X2)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq279246 (M.op X1 X2) X1 x
       have i₂ := eq229299 X1 X0 X2 x
       grind)
    | (have i₁ := eq279246 (M.op X1 X2) X1 X2
       have i₂ := eq229299 X0 (M.op X1 X2) X2 x
       grind)
    | exact superpose eq229299 eq279246
    | (have j1 := eq229299 X1 X0 X2 x
       grind)
    | exact resolve eq279246 eq229299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229299
  have eq448815 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y y) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq448559 X0 X1 x
       have i₂ := eq279264 y X1 x
       grind)
    | exact superpose eq279264 eq448559
    | (have j0 := eq448559 X0 X1 x
       grind)
    | exact resolve eq448559 eq279264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448559
  have eq483130 : ∀ X0 X1 X3 : G, (M.op X0 y) ≠ X0 ∨ (k X0 X3) = X0 ∨ (M.op X1 X3) = (k X1 X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2458 X1 x X0 X3
       have i₂ := eq279247 X1 x X0
       grind)
    | exact superpose eq279247 eq2458
    | (have j0 := eq2458 X1 X1 X0 X3
       grind)
    | exact resolve eq2458 eq279247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2458
  have eq495175 : ∀ X0 : G, y = (k y y) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq448378 x X0
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq448378
    | (have j0 := eq448378 x X0
       grind)
    | exact resolve eq448378 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448378
  have eq495363 : ∀ X0 : G, y ≠ y ∨ y = (σ (M.op (τ y) (τ y))) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq419925 y
       have i₂ := eq495175 X0
       grind)
    | exact superpose eq495175 eq419925
    | (have j0 := eq419925 y
       have j1 := eq495175 X0
       grind)
    | (have r₁ := eq419925 y
       have r₂ := eq495175 X0
       grind)
    | exact resolve eq419925 eq495175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419925
  have eq495365 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 y y
       have i₂ := eq495175 X0
       grind)
    | exact superpose eq495175 eq12
    | (have j0 := eq12 y y
       have j1 := eq495175 X0
       grind)
    | exact resolve eq12 eq495175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495175
  have eq495395 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq495365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495365
  have eq495397 : ∀ X0 : G, y = (σ (M.op (τ y) (τ y))) ∨ (M.op X0 x) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq495363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495363
  have eq497013 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y (σ X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq381188
       have i₂ := eq45806 y x
       grind)
    | (have i₁ := eq381188
       have i₂ := eq45806 X0 (τ (M.op y y))
       grind)
    | exact superpose eq45806 eq381188
    | (have j1 := eq45806 y X0
       grind)
    | exact resolve eq381188 eq45806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497349 : ∀ X0 : G, (M.op y X0) = (M.op X0 (τ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq279246 X0 (τ (M.op y y)) (τ (M.op y y))
       have i₂ := eq381188
       grind)
    | exact superpose eq381188 eq279246
    | exact resolve eq279246 eq381188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497353 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (τ (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq279264 X0 (τ (M.op y y)) (τ (M.op y y))
       have i₂ := eq381188
       grind)
    | exact superpose eq381188 eq279264
    | exact resolve eq279264 eq381188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497784 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op y X1) ∨ (M.op y X0) = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq497349 X1
       have i₂ := eq81428 X0 y
       grind)
    | (have i₁ := eq497349 X0
       have i₂ := eq81428 (M.op y y) X1
       grind)
    | exact superpose eq81428 eq497349
    | (have j1 := eq81428 X0 y
       grind)
    | exact resolve eq497349 eq81428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498627 : (τ (M.op y y)) = (M.op y (τ (M.op y y))) := by
    first
    | (have i₁ := eq381188
       have i₂ := eq497349 (τ (M.op y y))
       grind)
    | exact superpose eq497349 eq381188
    | exact resolve eq381188 eq497349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381188 eq497349
  have eq498673 : (M.op y y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq498627
       have i₂ := eq497353 y
       grind)
    | exact superpose eq497353 eq498627
    | exact resolve eq498627 eq497353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497353 eq498627
  have eq498917 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq498673
       have i₂ := eq448815 y X1
       grind)
    | (have i₁ := eq498673
       have i₂ := eq448815 X0 X1
       grind)
    | exact superpose eq448815 eq498673
    | (have j1 := eq448815 X0 X1
       grind)
    | exact resolve eq498673 eq448815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498927 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq81428 X0 y
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq81428
    | (have j0 := eq81428 X0 y
       grind)
    | exact resolve eq81428 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81428
  have eq498928 : ∀ X0 : G, (M.op y (σ X0)) = (k y (σ X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq45806 y X0
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq45806
    | (have j0 := eq45806 y X0
       grind)
    | exact resolve eq45806 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45806
  have eq498929 : (M.op y y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq10
    | exact resolve eq10 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498937 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq86 (M.op y y) X0
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq86
    | exact resolve eq86 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498938 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq86 X0 (M.op y y)
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq86
    | exact resolve eq86 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499036 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X0 X0)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq498929
       have i₂ := eq448815 y X1
       grind)
    | (have i₁ := eq498929
       have i₂ := eq448815 X0 X1
       grind)
    | exact superpose eq448815 eq498929
    | (have j1 := eq448815 X0 X1
       grind)
    | exact resolve eq498929 eq448815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448815
  have eq503978 : (τ y) = (k (τ y) (M.op y y)) := by grind
  clear eq498937
  have eq505382 : ∀ X0 X1 : G, (τ (M.op y y)) = (k (M.op y y) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq498938 (M.op X0 X1)
       have i₂ := eq431076 X0 X1
       grind)
    | exact superpose eq431076 eq498938
    | exact resolve eq498938 eq431076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431076
  have eq505386 : (τ (M.op y y)) = (k (M.op y y) (τ y)) := by
    first
    | (have i₁ := eq498938 y
       have i₂ := eq431000 y
       grind)
    | exact superpose eq431000 eq498938
    | exact resolve eq498938 eq431000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431000 eq498938
  have eq505527 : (M.op y y) = (k (M.op y y) (τ y)) := by
    first
    | (have i₁ := eq505386
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq505386
    | exact resolve eq505386 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505386
  have eq505531 : ∀ X0 X1 : G, (M.op y y) = (k (M.op y y) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq505382 X0 X1
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq505382
    | exact resolve eq505382 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505382
  have eq506007 : (M.op y y) = (M.op (M.op y y) (τ y)) ∨ (M.op y y) = (M.op y (τ y)) := by
    first
    | (have i₁ := eq279418 (τ y) (M.op y y)
       have i₂ := eq505527
       grind)
    | exact superpose eq505527 eq279418
    | (have j0 := eq279418 (τ y) x
       grind)
    | exact resolve eq279418 eq505527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505527
  have eq506025 : (M.op y y) = (M.op y (τ y)) ∨ (M.op y y) = (M.op y (τ y)) := by
    first
    | (have i₁ := eq506007
       have i₂ := eq279249 y y (τ y)
       grind)
    | exact superpose eq279249 eq506007
    | exact resolve eq506007 eq279249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506007
  have eq506026 : (M.op y y) = (M.op y (τ y)) := by grind
  clear eq506025
  have eq508199 : ∀ X0 X1 : G, (M.op y y) = (M.op (M.op y y) (τ (M.op X0 X1))) ∨ (M.op y y) = (M.op y (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq279418 (τ (M.op X0 X1)) (M.op y y)
       have i₂ := eq505531 X0 X1
       grind)
    | exact superpose eq505531 eq279418
    | (have j0 := eq279418 (τ (M.op X0 X1)) x
       grind)
    | exact resolve eq279418 eq505531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279418 eq505531
  have eq508212 : ∀ X0 X1 : G, (M.op y y) = (M.op y (τ (M.op X0 X1))) ∨ (M.op y y) = (M.op y (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq508199 X0 X1
       have i₂ := eq279249 y y (τ (M.op X0 X1))
       grind)
    | exact superpose eq279249 eq508199
    | (have j0 := eq508199 X0 X1
       grind)
    | exact resolve eq508199 eq279249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279249 eq508199
  have eq508213 : ∀ X0 X1 : G, (M.op y y) = (M.op y (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq508212 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508212
  have eq531502 : ∀ X0 : G, (σ (τ y)) = (k (σ (τ y)) X0) ∨ (k (σ y) X0) = (σ (M.op y (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13153 y (τ y) X0
       have i₂ := eq503978
       grind)
    | exact superpose eq503978 eq13153
    | (have j0 := eq13153 y x X0
       grind)
    | exact resolve eq13153 eq503978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13153
  have eq531518 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq531502 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq531502
    | (have j0 := eq531502 X0
       grind)
    | exact resolve eq531502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531502
  have eq532048 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k (τ y) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq32 y X0
       have i₂ := eq497013 X0
       grind)
    | exact superpose eq497013 eq32
    | (have j1 := eq497013 X0
       grind)
    | exact resolve eq32 eq497013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497013
  have eq539070 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq419930 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq419930
    | (have j0 := eq419930 X1 (σ X0)
       grind)
    | exact resolve eq419930 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419930
  have eq539842 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (σ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq498929
       have i₂ := eq539070 X0 y
       grind)
    | (have i₁ := eq498929
       have i₂ := eq539070 (M.op y y) x
       grind)
    | exact superpose eq539070 eq498929
    | (have j1 := eq539070 X0 y
       grind)
    | exact resolve eq498929 eq539070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539070
  have eq545392 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq15873 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15873
  have eq545393 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq545392 X0 X1
       have j1 := eq3265 X1 X0
       grind)
    | (have r₁ := eq545392 (k X1 X1) X0
       have r₂ := eq3265 X0 X1
       grind)
    | (have r₁ := eq545392 X0 (σ (k X1 X1))
       have r₂ := eq3265 (σ X0) X1
       grind)
    | (have r₁ := eq545392 X1 X0
       have r₂ := eq3265 X0 X1
       grind)
    | exact resolve eq545392 eq3265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3265 eq545392
  have eq545440 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq545393 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq545393 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq545393 eq16
    | (have j1 := eq545393 (τ X1) X0
       grind)
    | exact resolve eq16 eq545393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545441 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq545393 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq545393 X0 (σ X0)
       grind)
    | exact superpose eq545393 eq9
    | (have j1 := eq545393 X1 X0
       grind)
    | exact resolve eq9 eq545393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545393
  have eq545472 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq545440 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq545440
    | (have j0 := eq545440 X0 X1
       grind)
    | exact resolve eq545440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545440
  have eq545486 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq545472 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq545472
    | (have j0 := eq545472 X0 X1
       grind)
    | exact resolve eq545472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545472
  have eq545770 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq15867
       have i₂ := eq545486 y x
       grind)
    | exact superpose eq545486 eq15867
    | (have j1 := eq545486 y x
       grind)
    | exact resolve eq15867 eq545486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15867
  have eq545775 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq3281
       have i₂ := eq545486 y x
       grind)
    | exact superpose eq545486 eq3281
    | (have j1 := eq545486 y x
       grind)
    | exact resolve eq3281 eq545486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq545889 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq545486 X0 (τ X1)
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq545486 (k (τ X0) X1) X1
       grind)
    | exact superpose eq545486 eq16
    | (have j1 := eq545486 X0 (τ X1)
       grind)
    | exact resolve eq16 eq545486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545924 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by grind
  clear eq545775
  have eq545925 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq545770
  have eq545933 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (k (τ X1) X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq545889 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq545889
    | (have j0 := eq545889 X0 X1
       grind)
    | exact resolve eq545889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545889
  have eq546909 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq165 (σ x) (σ x)
       have i₂ := eq545924
       grind)
    | exact superpose eq545924 eq165
    | (have j0 := eq165 (σ x) (σ x)
       grind)
    | exact resolve eq165 eq545924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547085 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq279246 X0 (σ x) (σ x)
       have i₂ := eq545924
       grind)
    | exact superpose eq545924 eq279246
    | exact resolve eq279246 eq545924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545924
  have eq547234 : (σ x) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq546909
       have r₂ := eq421181
       grind)
    | exact resolve eq546909 eq421181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421181 eq546909
  have eq547348 : (σ x) = (σ (k x x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq547234
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq547234
    | exact resolve eq547234 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547234
  have eq548465 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq3380 x
       have i₂ := eq547348
       grind)
    | exact superpose eq547348 eq3380
    | (have j0 := eq3380 x
       grind)
    | (have r₁ := eq3380 x
       have r₂ := eq547348
       grind)
    | exact resolve eq3380 eq547348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3380 eq547348
  have eq548496 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by grind
  clear eq548465
  have eq549897 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ x)) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq279246 X0 (σ x) (σ x)
       have i₂ := eq548496
       grind)
    | exact superpose eq548496 eq279246
    | exact resolve eq279246 eq548496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551709 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq547085 (σ x)
       grind)
    | exact superpose eq547085 eq14
    | exact resolve eq14 eq547085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547085
  have eq555426 : (σ x) = (M.op y (σ x)) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq548496
       have i₂ := eq549897 (σ x)
       grind)
    | exact superpose eq549897 eq548496
    | exact resolve eq548496 eq549897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548496 eq549897
  have eq555470 : (σ x) = (M.op y (σ x)) ∨ y = (k x x) := by grind
  clear eq555426
  have eq560818 : (σ x) ≠ (M.op y (σ x)) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq551709
       have i₂ := eq545925
       grind)
    | exact superpose eq545925 eq551709
    | exact resolve eq551709 eq545925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545925 eq551709
  have eq560822 : (σ x) ≠ (M.op y (σ x)) ∨ y = (k x x) := by grind
  clear eq560818
  have eq560825 : y = (k x x) := by
    first
    | (have r₁ := eq560822
       have r₂ := eq555470
       grind)
    | exact resolve eq560822 eq555470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555470 eq560822
  have eq560925 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq545486 X0 x
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq545486
    | (have j0 := eq545486 X0 x
       grind)
    | exact resolve eq545486 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561935 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k (τ x) X0) ∨ (σ X0) = y := by
    intro X0
    first
    | (have i₁ := eq32 x X0
       have i₂ := eq560925 (σ X0)
       grind)
    | exact superpose eq560925 eq32
    | (have j1 := eq560925 (σ X0)
       grind)
    | exact resolve eq32 eq560925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq560925
  have eq565595 : ∀ X0 : G, (τ (M.op x X0)) = (k (τ x) (τ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq561935 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq561935
    | exact resolve eq561935 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561935
  have eq565624 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k x X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq565595 X0
       have i₂ := eq86 X0 x
       grind)
    | exact superpose eq86 eq565595
    | (have j0 := eq565595 X0
       grind)
    | exact resolve eq565595 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565595
  have eq567326 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X1)) ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 X1
       have i₂ := eq545441 X0 (τ X1)
       grind)
    | exact superpose eq545441 eq86
    | (have j1 := eq545441 X0 (τ X1)
       grind)
    | exact resolve eq86 eq545441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545441
  have eq567352 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (τ X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq567326 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq567326
    | (have j0 := eq567326 X0 X1
       grind)
    | exact resolve eq567326 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567326
  have eq568070 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X1 X0
       have i₂ := eq545933 (τ X1) X0
       grind)
    | exact superpose eq545933 eq86
    | (have j1 := eq545933 (τ X1) X0
       grind)
    | exact resolve eq86 eq545933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545933
  have eq568086 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq568070 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq568070
    | (have j0 := eq568070 X0 X1
       grind)
    | exact resolve eq568070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568070
  have eq571254 : ∀ X0 X1 X2 : G, (M.op (τ (k X0 X1)) X2) = (M.op X2 y) ∨ (k X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq279247 (τ X0) (τ X1) X2
       have i₂ := eq568086 X0 X1
       grind)
    | exact superpose eq568086 eq279247
    | (have j1 := eq568086 X0 X1
       grind)
    | exact resolve eq279247 eq568086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568086
  have eq582229 : ∀ X0 : G, (σ X0) = (M.op y (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18629 X0
       have i₂ := eq283037 X0 (σ X0)
       grind)
    | exact superpose eq283037 eq18629
    | (have j0 := eq18629 X0
       have j1 := eq283037 X0 x
       grind)
    | exact resolve eq18629 eq283037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18629 eq283037
  have eq582305 : ∀ X0 : G, (σ X0) = (M.op y (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq582229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582229
  have eq584814 : ∀ X0 : G, (τ X0) = (M.op y (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq101489 X0
       have i₂ := eq283043 X0 (τ X0)
       grind)
    | exact superpose eq283043 eq101489
    | (have j0 := eq101489 X0
       have j1 := eq283043 X0 x
       grind)
    | exact resolve eq101489 eq283043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101489
  have eq584863 : ∀ X0 : G, (τ X0) = (M.op y (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq584814 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584814
  have eq585013 : ∀ X0 : G, (τ X0) = (M.op y y) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq283043 X0 y
       have i₂ := eq584863 X0
       grind)
    | exact superpose eq584863 eq283043
    | (have j0 := eq283043 X0 x
       have j1 := eq584863 X0
       grind)
    | exact resolve eq283043 eq584863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283043
  have eq585248 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq585013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585013
  have eq585456 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (τ (σ X0)) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq585248 (σ X0)
       grind)
    | exact superpose eq585248 eq13
    | (have j1 := eq585248 (σ X0)
       grind)
    | exact resolve eq13 eq585248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585248
  have eq585505 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq585456 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq585456
    | (have j0 := eq585456 X0
       grind)
    | exact resolve eq585456 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585456
  have eq598507 : ∀ X0 : G, y = (k y (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq298452 X0
       have i₂ := eq582305 X0
       grind)
    | exact superpose eq582305 eq298452
    | (have j0 := eq298452 X0
       have j1 := eq582305 X0
       grind)
    | exact resolve eq298452 eq582305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298452 eq582305
  have eq598539 : ∀ X0 : G, y = (k y (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq598507 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598507
  have eq598681 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ y = (k y (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0 X0
       have i₂ := eq598539 (τ X0)
       grind)
    | exact superpose eq598539 eq86
    | (have j1 := eq598539 (τ X0)
       grind)
    | exact resolve eq86 eq598539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598539
  have eq598684 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq598681 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq598681
    | (have j0 := eq598681 X0
       grind)
    | exact resolve eq598681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598681
  have eq599057 : ∀ X0 : G, y = (k y (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq298458 X0
       have i₂ := eq584863 X0
       grind)
    | exact superpose eq584863 eq298458
    | (have j0 := eq298458 X0
       have j1 := eq584863 X0
       grind)
    | exact resolve eq298458 eq584863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298458 eq584863
  have eq599086 : ∀ X0 : G, y = (k y (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq599057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599057
  have eq599285 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ y = (k y (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq599086 (σ X0)
       grind)
    | exact superpose eq599086 eq13
    | (have j1 := eq599086 (σ X0)
       grind)
    | exact resolve eq13 eq599086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599086
  have eq599293 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq599285 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq599285
    | (have j0 := eq599285 X0
       grind)
    | exact resolve eq599285 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599285
  have eq618677 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (τ (M.op x X0)) X1) ∨ (k x x) = X0 ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571254 x X0 X1
       have i₂ := eq565624 X0
       grind)
    | exact superpose eq565624 eq571254
    | (have j0 := eq571254 x X0 x
       have j1 := eq565624 X0
       grind)
    | exact resolve eq571254 eq565624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565624 eq571254
  have eq618944 : ∀ X0 X1 : G, y = X0 ∨ (M.op X1 y) = (M.op (τ (M.op x X0)) X1) ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq618677 X0 X1
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq618677
    | (have j0 := eq618677 X0 X1
       grind)
    | exact resolve eq618677 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618677
  have eq618945 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (τ (M.op x X0)) X1) ∨ y = X0 := by
    intro X0 X1
    first
    | (have j0 := eq618944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618944
  have eq619054 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (τ (M.op x y)) X0) ∨ (M.op X1 X2) = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq618945 (M.op X1 X2) X0
       have i₂ := eq279264 x X1 X2
       grind)
    | exact superpose eq279264 eq618945
    | (have j0 := eq618945 y X0
       grind)
    | exact resolve eq618945 eq279264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618945
  have eq654529 : ∀ X0 X1 : G, (M.op y X0) ≠ X0 ∨ (k X0 (τ X1)) = X0 ∨ (M.op y X1) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 (τ X1)
       have i₂ := eq497784 X1 X0
       grind)
    | exact superpose eq497784 eq165
    | (have j0 := eq165 X0 (τ X1)
       have j1 := eq497784 X1 X1
       grind)
    | exact resolve eq165 eq497784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497784
  have eq655638 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (τ (M.op y (σ (τ X0)))) = (k (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq532048 (τ X0)
       grind)
    | exact superpose eq532048 eq33
    | (have j1 := eq532048 (τ X0)
       grind)
    | exact resolve eq33 eq532048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq532048
  have eq655641 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (M.op y (σ (τ X0)))) = (k (τ y) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq655638 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq655638
    | (have j0 := eq655638 X0
       grind)
    | exact resolve eq655638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655638
  have eq655671 : ∀ X0 : G, (τ (k y X0)) = (τ (M.op y (σ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq655641 X0
       have i₂ := eq86 X0 y
       grind)
    | exact superpose eq86 eq655641
    | (have j0 := eq655641 X0
       grind)
    | exact resolve eq655641 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq655641
  have eq655673 : ∀ X0 : G, (τ (k y X0)) = (τ (M.op y X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq655671 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq655671
    | (have j0 := eq655671 X0
       grind)
    | exact resolve eq655671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655671
  have eq658627 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (σ (k X0 X0))) ∨ (M.op y y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq279246 X1 (σ X0) (σ X0)
       have i₂ := eq585505 X0
       grind)
    | exact superpose eq585505 eq279246
    | (have j1 := eq585505 X0
       grind)
    | exact resolve eq279246 eq585505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585505
  have eq659935 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (τ (k X0 X0))) ∨ y = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279246 X1 (τ X0) (τ X0)
       have i₂ := eq598684 X0
       grind)
    | exact superpose eq598684 eq279246
    | (have j1 := eq598684 X0
       grind)
    | exact resolve eq279246 eq598684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659936 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (τ (k X0 X0)) X1) ∨ y = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279247 (τ X0) (τ X0) X1
       have i₂ := eq598684 X0
       grind)
    | exact superpose eq598684 eq279247
    | (have j1 := eq598684 X0
       grind)
    | exact resolve eq279247 eq598684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279247 eq598684
  have eq661040 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (σ (k X0 X0))) ∨ y = (k y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq279246 X1 (σ X0) (σ X0)
       have i₂ := eq599293 X0
       grind)
    | exact superpose eq599293 eq279246
    | (have j1 := eq599293 X0
       grind)
    | exact resolve eq279246 eq599293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279246 eq599293
  have eq673055 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq498917 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq498917
    | (have j0 := eq498917 x X0
       grind)
    | exact resolve eq498917 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498917
  have eq673282 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq673055 (τ X0)
       grind)
    | exact superpose eq673055 eq16
    | exact resolve eq16 eq673055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682047 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq658627 x X0
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq658627
    | (have j0 := eq658627 x x
       grind)
    | exact resolve eq658627 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658627
  have eq682824 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq682047 (σ x)
       grind)
    | exact superpose eq682047 eq14
    | exact resolve eq14 eq682047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682047
  have eq686746 : ∀ X0 : G, (M.op y X0) = (M.op X0 (τ y)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq659935 x X0
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq659935
    | (have j0 := eq659935 x x
       grind)
    | exact resolve eq659935 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659935
  have eq687273 : ∀ X0 : G, y = (σ (M.op y (τ y))) ∨ (M.op X0 x) = (k X0 x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq495397 X0
       have i₂ := eq686746 (τ y)
       grind)
    | exact superpose eq686746 eq495397
    | (have j0 := eq495397 X0
       grind)
    | exact resolve eq495397 eq686746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495397 eq686746
  have eq687335 : ∀ X0 : G, y = (σ (M.op y y)) ∨ (M.op X0 x) = (k X0 x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq687273 X0
       have i₂ := eq506026
       grind)
    | exact superpose eq506026 eq687273
    | (have j0 := eq687273 X0
       grind)
    | exact resolve eq687273 eq506026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506026 eq687273
  have eq687433 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 x) = (k X0 x) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq687335 X0
       have i₂ := eq498929
       grind)
    | exact superpose eq498929 eq687335
    | (have j0 := eq687335 X0
       grind)
    | exact resolve eq687335 eq498929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498929 eq687335
  have eq687495 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (k y x) := by
    intro X0
    first
    | (have j0 := eq687433 X0
       have j1 := eq483130 y X0 x
       grind)
    | (have r₁ := eq687433 X0
       have r₂ := eq483130 y x x
       grind)
    | exact resolve eq687433 eq483130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483130 eq687433
  have eq687587 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq687495 (τ X0)
       grind)
    | exact superpose eq687495 eq16
    | exact resolve eq16 eq687495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687495
  have eq687677 : ∀ X0 : G, (M.op X0 y) = (M.op (τ y) X0) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq659936 x X0
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq659936
    | (have j0 := eq659936 x x
       grind)
    | exact resolve eq659936 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659936
  have eq690076 : ∀ X0 : G, (M.op y X0) = (M.op X0 (σ y)) ∨ y = (k y x) := by
    intro X0
    first
    | (have i₁ := eq661040 x X0
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq661040
    | (have j0 := eq661040 x x
       grind)
    | exact resolve eq661040 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661040
  have eq690606 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq690076 (σ x)
       grind)
    | exact superpose eq690076 eq14
    | exact resolve eq14 eq690076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690076
  have eq695652 : ∀ X0 : G, (M.op X0 x) = (k X0 x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq499036 x x
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq499036
    | (have j0 := eq499036 x X0
       grind)
    | exact resolve eq499036 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499036
  have eq695892 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x
       have i₂ := eq695652 (τ X0)
       grind)
    | exact superpose eq695652 eq16
    | exact resolve eq16 eq695652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695652
  have eq696165 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op X0 x)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq695892 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq695892
    | exact resolve eq695892 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695892
  have eq696211 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq696165 X0
       have i₂ := eq13 X0 x
       grind)
    | exact superpose eq13 eq696165
    | exact resolve eq696165 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696165
  have eq708065 : ∀ X0 : G, (τ (k (σ y) X0)) = (M.op y (τ X0)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op y (τ X0))
       have i₂ := eq531518 X0
       grind)
    | exact superpose eq531518 eq9
    | (have j1 := eq531518 X0
       grind)
    | exact resolve eq9 eq531518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531518
  have eq708066 : ∀ X0 : G, (k y (τ X0)) = (M.op y (τ X0)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq708065 X0
       have i₂ := eq51 y X0
       grind)
    | exact superpose eq51 eq708065
    | (have j0 := eq708065 X0
       grind)
    | exact resolve eq708065 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq708065
  have eq708105 : y = (M.op y (τ (M.op (σ y) (σ y)))) ∨ y = (k y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq708066 (M.op (σ y) (σ y))
       grind)
    | exact superpose eq708066 eq187
    | (have j1 := eq708066 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq187 eq708066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708066
  have eq708111 : y = (M.op y y) ∨ y = (k y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq708105
       have i₂ := eq508213 (σ y) (σ y)
       grind)
    | exact superpose eq508213 eq708105
    | exact resolve eq708105 eq508213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708105
  have eq708113 : y = (k y (M.op (σ y) (σ y))) := by
    first
    | (have j1 := eq279332 y (σ y) (σ y)
       grind)
    | (have r₁ := eq708111
       have r₂ := eq279332 y x x
       grind)
    | exact resolve eq708111 eq279332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279332 eq708111
  have eq708196 : y = (M.op y (M.op (σ y) (σ y))) ∨ (M.op (σ y) (σ y)) = (k y y) := by
    first
    | (have i₁ := eq545486 (M.op (σ y) (σ y)) y
       have i₂ := eq708113
       grind)
    | exact superpose eq708113 eq545486
    | (have j0 := eq545486 (M.op (σ y) (σ y)) y
       grind)
    | exact resolve eq545486 eq708113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545486 eq708113
  have eq708208 : (M.op (σ y) (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq708196
       have i₂ := eq279264 y (σ y) (σ y)
       grind)
    | exact superpose eq279264 eq708196
    | exact resolve eq708196 eq279264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279264 eq708196
  have eq708528 : y = (k y (τ (k y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq187 y
       have i₂ := eq708208
       grind)
    | exact superpose eq708208 eq187
    | exact resolve eq187 eq708208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq708208
  have eq708961 : ∀ X0 : G, y = (k y (τ X0)) ∨ y = (M.op y y) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq708528
       have i₂ := eq567352 X0 y
       grind)
    | (have i₁ := eq708528
       have i₂ := eq567352 (k y y) x
       grind)
    | exact superpose eq567352 eq708528
    | (have j1 := eq567352 X0 y
       grind)
    | exact resolve eq708528 eq567352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567352 eq708528
  have eq708985 : ∀ X0 : G, y = (k y (τ X0)) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq708961 X0
       have j1 := eq654529 y X0
       grind)
    | (have r₁ := eq708961 X0
       have r₂ := eq654529 y x
       grind)
    | exact resolve eq708961 eq654529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654529 eq708961
  have eq709608 : ∀ X0 : G, (M.op y (σ X0)) = (k y (σ X0)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq708985 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq708985
    | (have j0 := eq708985 (σ X0)
       grind)
    | exact resolve eq708985 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708985
  have eq718274 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (M.op (τ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq619054 X0 (τ (M.op x y)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619054
  have eq720897 : (σ (M.op x y)) = (k y (σ x)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq687587 y
       have i₂ := eq687677 x
       grind)
    | exact superpose eq687677 eq687587
    | exact resolve eq687587 eq687677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687587 eq687677
  have eq720904 : (σ (M.op x y)) = (k y (σ x)) ∨ y = (k y x) := by grind
  clear eq720897
  have eq720935 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (k y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq709608 x
       have i₂ := eq720904
       grind)
    | exact superpose eq720904 eq709608
    | (have j0 := eq709608 x
       grind)
    | exact resolve eq709608 eq720904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709608 eq720904
  have eq720937 : (σ (M.op x y)) = (M.op y (σ x)) ∨ y = (k y x) := by grind
  clear eq720935
  have eq720940 : y = (k y x) := by
    first
    | (have r₁ := eq720937
       have r₂ := eq690606
       grind)
    | exact resolve eq720937 eq690606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690606 eq720937
  have eq720992 : y = (M.op y x) ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq539842 x
       have i₂ := eq720940
       grind)
    | exact superpose eq720940 eq539842
    | (have j0 := eq539842 x
       grind)
    | exact resolve eq539842 eq720940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539842
  have eq721002 : y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq495395 y
       have i₂ := eq720940
       grind)
    | exact superpose eq720940 eq495395
    | exact resolve eq495395 eq720940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495395
  have eq721009 : y = (M.op y x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq673055 y
       have i₂ := eq720940
       grind)
    | exact superpose eq720940 eq673055
    | exact resolve eq673055 eq720940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720940
  have eq721082 : y = (M.op x y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq721009
       have i₂ := eq283061 x
       grind)
    | exact superpose eq283061 eq721009
    | exact resolve eq721009 eq283061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721009
  have eq721089 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq721002
       have i₂ := eq283061 x
       grind)
    | exact superpose eq283061 eq721002
    | exact resolve eq721002 eq283061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721002
  have eq721099 : (σ x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq720992
       have i₂ := eq283061 x
       grind)
    | exact superpose eq283061 eq720992
    | exact resolve eq720992 eq283061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720992
  have eq722029 : y ≠ y ∨ y = (M.op (τ y) x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq718274 x
       have i₂ := eq721082
       grind)
    | exact superpose eq721082 eq718274
    | (have r₁ := eq718274 x
       have r₂ := eq721082
       grind)
    | exact resolve eq718274 eq721082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721082
  have eq722302 : y = (M.op (τ y) x) ∨ y = (τ y) := by grind
  clear eq722029
  have eq729108 : (σ y) = (k y (σ x)) ∨ y = (τ y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq673282 y
       have i₂ := eq722302
       grind)
    | exact superpose eq722302 eq673282
    | exact resolve eq673282 eq722302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673282 eq722302
  have eq729374 : (σ y) = (k y (σ x)) ∨ y = (τ y) := by grind
  clear eq729108
  have eq737219 : y = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq721089
       have i₂ := eq721099
       grind)
    | exact superpose eq721099 eq721089
    | exact resolve eq721089 eq721099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721089
  have eq737364 : (σ x) = (M.op y (τ (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq508213 y y
       have i₂ := eq721099
       grind)
    | exact superpose eq721099 eq508213
    | exact resolve eq508213 eq721099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508213 eq721099
  have eq737371 : y = (M.op x y) ∨ y = (σ x) := by grind
  clear eq737219
  have eq737382 : (σ x) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq737364
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq737364
    | exact resolve eq737364 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737364
  have eq737447 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq737382
       have i₂ := eq283061 x
       grind)
    | exact superpose eq283061 eq737382
    | exact resolve eq737382 eq283061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737382
  have eq745751 : y ≠ (σ x) ∨ y = (M.op x y) := by grind
  clear eq737447
  have eq745753 : y = (M.op x y) := by
    first
    | (have r₁ := eq745751
       have r₂ := eq737371
       grind)
    | exact resolve eq745751 eq737371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737371 eq745751
  have eq745827 : (σ y) ≠ (M.op y (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq682824
       have i₂ := eq745753
       grind)
    | exact superpose eq745753 eq682824
    | exact resolve eq682824 eq745753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682824
  have eq745880 : y ≠ y ∨ y = (M.op (τ y) x) := by
    first
    | (have i₁ := eq718274 x
       have i₂ := eq745753
       grind)
    | exact superpose eq745753 eq718274
    | (have r₁ := eq718274 x
       have r₂ := eq745753
       grind)
    | exact resolve eq718274 eq745753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718274
  have eq746329 : y = (M.op (τ y) x) := by grind
  clear eq745880
  have eq746550 : y ≠ (τ y) ∨ (τ y) = (k (τ y) x) := by
    first
    | (have i₁ := eq165 (τ y) x
       have i₂ := eq746329
       grind)
    | exact superpose eq746329 eq165
    | (have j0 := eq165 (τ y) x
       grind)
    | exact resolve eq165 eq746329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq749776 : (σ y) = (M.op y (σ x)) ∨ x = (M.op y y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq498928 x
       have i₂ := eq729374
       grind)
    | exact superpose eq729374 eq498928
    | (have j0 := eq498928 x
       grind)
    | exact resolve eq498928 eq729374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498928 eq729374
  have eq749826 : x = (M.op y y) ∨ y = (τ y) := by
    first
    | (have r₁ := eq749776
       have r₂ := eq745827
       grind)
    | exact resolve eq749776 eq745827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745827 eq749776
  have eq749868 : (τ y) = (k (τ y) x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq503978
       have i₂ := eq749826
       grind)
    | exact superpose eq749826 eq503978
    | exact resolve eq503978 eq749826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503978 eq749826
  have eq750352 : (τ y) = (k (τ y) x) := by
    first
    | (have r₁ := eq749868
       have r₂ := eq746550
       grind)
    | exact resolve eq749868 eq746550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746550 eq749868
  have eq750745 : (k y (σ x)) = (σ (τ y)) := by
    first
    | (have i₁ := eq16 y x
       have i₂ := eq750352
       grind)
    | exact superpose eq750352 eq16
    | exact resolve eq16 eq750352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq750777 : (τ y) = (M.op (τ y) x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq673055 (τ y)
       have i₂ := eq750352
       grind)
    | exact superpose eq750352 eq673055
    | exact resolve eq673055 eq750352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673055
  have eq750784 : (σ (τ y)) = (σ (M.op (τ y) x)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq696211 (τ y)
       have i₂ := eq750352
       grind)
    | exact superpose eq750352 eq696211
    | exact resolve eq696211 eq750352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696211 eq750352
  have eq750833 : (σ y) = (σ (τ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq750784
       have i₂ := eq746329
       grind)
    | exact superpose eq746329 eq750784
    | exact resolve eq750784 eq746329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750784
  have eq750838 : y = (τ y) ∨ y = (τ y) := by
    first
    | (have i₁ := eq750777
       have i₂ := eq746329
       grind)
    | exact superpose eq746329 eq750777
    | exact resolve eq750777 eq746329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746329 eq750777
  have eq750839 : y = (τ y) := by grind
  clear eq750838
  have eq750871 : y = (k y (σ x)) := by
    first
    | (have i₁ := eq750745
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq750745
    | exact resolve eq750745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750745
  have eq750909 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq750833
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq750833
    | exact resolve eq750833 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750833
  have eq750910 : y = (σ y) := by grind
  clear eq750909
  have eq751134 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq750910
       grind)
    | exact superpose eq750910 eq14
    | exact resolve eq14 eq750910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751381 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq751134
       have i₂ := eq283061 (σ x)
       grind)
    | exact superpose eq283061 eq751134
    | exact resolve eq751134 eq283061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283061 eq751134
  have eq751391 : (σ y) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq751381
       have i₂ := eq745753
       grind)
    | exact superpose eq745753 eq751381
    | exact resolve eq751381 eq745753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745753 eq751381
  have eq751393 : y ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq751391
       have i₂ := eq750910
       grind)
    | exact superpose eq750910 eq751391
    | exact resolve eq751391 eq750910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751391
  have eq751431 : y = (M.op y (σ x)) ∨ (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq498927 (σ x)
       have i₂ := eq750871
       grind)
    | exact superpose eq750871 eq498927
    | (have j0 := eq498927 (σ x)
       grind)
    | exact resolve eq498927 eq750871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498927
  have eq751435 : (τ y) = (τ (M.op y (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq655673 (σ x)
       have i₂ := eq750871
       grind)
    | exact superpose eq750871 eq655673
    | (have j0 := eq655673 (σ x)
       grind)
    | exact resolve eq655673 eq750871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655673
  have eq751448 : y = (M.op y (σ x)) ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y (σ x)
       have i₂ := eq750871
       grind)
    | exact superpose eq750871 eq12
    | (have j0 := eq12 y (σ x)
       grind)
    | exact resolve eq12 eq750871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751458 : ∀ X0 : G, y = (M.op y (σ x)) ∨ (M.op X0 y) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq290409 X0 (σ x) y
       have i₂ := eq750871
       grind)
    | exact superpose eq750871 eq290409
    | (have j0 := eq290409 X0 (σ x) x
       grind)
    | exact resolve eq290409 eq750871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290409
  have eq751459 : ∀ X0 : G, y = (M.op y (σ x)) ∨ (M.op X0 y) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq290418 X0 (σ x) y
       have i₂ := eq750871
       grind)
    | exact superpose eq750871 eq290418
    | (have j0 := eq290418 X0 (σ x) x
       grind)
    | exact resolve eq290418 eq750871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290418 eq750871
  have eq751488 : ∀ X0 : G, (M.op X0 y) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq751459 X0
       grind)
    | (have r₁ := eq751459 X0
       have r₂ := eq751393
       grind)
    | exact resolve eq751459 eq751393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751459
  have eq751489 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq751458 X0
       grind)
    | (have r₁ := eq751458 X0
       have r₂ := eq751393
       grind)
    | exact resolve eq751458 eq751393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751458
  have eq751499 : (σ x) = (M.op y y) := by
    first
    | (have r₁ := eq751448
       have r₂ := eq751393
       grind)
    | exact resolve eq751448 eq751393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751448
  have eq751509 : y = (τ (M.op y (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751435
       have i₂ := eq750839
       grind)
    | exact superpose eq750839 eq751435
    | exact resolve eq751435 eq750839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750839 eq751435
  have eq751513 : (τ (σ x)) = (M.op y y) := by
    first
    | (have r₁ := eq751431
       have r₂ := eq751393
       grind)
    | exact resolve eq751431 eq751393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751393 eq751431
  have eq751548 : y = (τ (M.op y y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751509
       have i₂ := eq751489 y
       grind)
    | exact superpose eq751489 eq751509
    | exact resolve eq751509 eq751489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751489 eq751509
  have eq751552 : (σ x) = (τ (σ x)) := by
    first
    | (have i₁ := eq751513
       have i₂ := eq751499
       grind)
    | exact superpose eq751499 eq751513
    | exact resolve eq751513 eq751499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751513
  have eq751564 : y = (M.op y y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751548
       have i₂ := eq498673
       grind)
    | exact superpose eq498673 eq751548
    | exact resolve eq751548 eq498673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498673 eq751548
  have eq751565 : x = (σ x) := by
    first
    | (have i₁ := eq751552
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq751552
    | exact resolve eq751552 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751552
  have eq751571 : y = (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751564
       have i₂ := eq751499
       grind)
    | exact superpose eq751499 eq751564
    | exact resolve eq751564 eq751499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751564
  have eq751575 : x = y ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq751571
       have i₂ := eq751565
       grind)
    | exact superpose eq751565 eq751571
    | exact resolve eq751571 eq751565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751571
  have eq751579 : (σ x) = (σ (k x x)) ∨ x = y := by
    first
    | (have i₁ := eq751575
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq751575
    | exact resolve eq751575 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751575
  have eq751583 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq751579
       have i₂ := eq560825
       grind)
    | exact superpose eq560825 eq751579
    | exact resolve eq751579 eq560825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560825 eq751579
  have eq751584 : y = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq751583
       have i₂ := eq750910
       grind)
    | exact superpose eq750910 eq751583
    | exact resolve eq751583 eq750910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751583
  have eq751585 : x = y ∨ x = y := by
    first
    | (have i₁ := eq751584
       have i₂ := eq751565
       grind)
    | exact superpose eq751565 eq751584
    | exact resolve eq751584 eq751565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751584
  have eq751586 : x = y := by grind
  clear eq751585
  have eq751587 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq751586
       grind)
    | exact superpose eq751586 eq14
    | exact resolve eq14 eq751586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752384 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq751587
       have i₂ := eq275066
       grind)
    | exact superpose eq275066 eq751587
    | exact resolve eq751587 eq275066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275066 eq751587
  have eq752515 : (σ y) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq752384
       have i₂ := eq751488 (σ x)
       grind)
    | exact superpose eq751488 eq752384
    | exact resolve eq752384 eq751488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752384
  have eq752585 : (σ y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq752515
       have i₂ := eq751488 y
       grind)
    | exact superpose eq751488 eq752515
    | exact resolve eq752515 eq751488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751488 eq752515
  have eq752613 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq752585
       have i₂ := eq751499
       grind)
    | exact superpose eq751499 eq752585
    | exact resolve eq752585 eq751499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751499 eq752585
  have eq752632 : y ≠ (σ x) := by
    first
    | (have i₁ := eq752613
       have i₂ := eq750910
       grind)
    | exact superpose eq750910 eq752613
    | exact resolve eq752613 eq750910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750910 eq752613
  have eq752646 : x ≠ y := by
    first
    | (have i₁ := eq752632
       have i₂ := eq751565
       grind)
    | exact superpose eq751565 eq752632
    | exact resolve eq752632 eq751565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751565 eq752632
  have eq752657 : False := by grind
  exact eq752657

/-- `Equation4541`: `x ◇ (y ◇ z) = (z ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation4541 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4541 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4541.models_iff G M).mp hM
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq117 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq117 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq117 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq139 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq121 (σ X0) (σ X1)
       grind)
    | exact superpose eq121 eq13
    | exact resolve eq13 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq139
    | exact resolve eq139 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq139
  have eq2573 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq146 x y
       grind)
    | exact superpose eq146 eq14
    | (have r₁ := eq14
       have r₂ := eq146 x y
       grind)
    | exact resolve eq14 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq2596 : False := by grind
  exact eq2596

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation455 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law455 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) X0
       have i₂ := eq8 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq23 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq84 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq20
    | exact resolve eq20 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq171 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq43 X2 X0
       grind)
    | exact superpose eq43 eq23
    | (have j1 := eq43 X2 X0
       grind)
    | exact resolve eq23 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq461 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq461
    | (have j0 := eq461 X0 X1
       grind)
    | exact resolve eq461 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq1218 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq172 (M.op X0 X0)
       have i₂ := eq32 X0 (M.op X0 X0)
       grind)
    | exact superpose eq32 eq172
    | (have j0 := eq172 (M.op X0 X0)
       grind)
    | exact resolve eq172 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1231 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq172 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq172
    | (have j0 := eq172 (τ X0)
       grind)
    | exact resolve eq172 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq172
  have eq1243 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1218 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1249 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1231 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1231
    | (have j0 := eq1231 X0
       grind)
    | exact resolve eq1231 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1258 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1249 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1249
    | (have j0 := eq1249 X0
       grind)
    | exact resolve eq1249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1421 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op X0 X0)) X1
       have i₂ := eq1243 X0
       grind)
    | exact superpose eq1243 eq23
    | exact resolve eq23 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1556 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1421 X0 X1
       have i₂ := eq509 X2 X0
       grind)
    | exact superpose eq509 eq1421
    | (have j1 := eq509 X2 X0
       grind)
    | exact resolve eq1421 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq1421
  have eq1769 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq171 y X0 x
       grind)
    | exact superpose eq171 eq14
    | (have j1 := eq171 y X0 x
       grind)
    | exact resolve eq14 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq1799 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1769 X0
       have j1 := eq1556 y X0 x
       grind)
    | (have r₁ := eq1769 X0
       have r₂ := eq1556 y x x
       grind)
    | exact resolve eq1769 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq1769
  have eq1814 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq84 (σ y) x
       have i₂ := eq1799 (σ y)
       grind)
    | exact superpose eq1799 eq84
    | exact resolve eq84 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1826 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1799 (σ x)
       grind)
    | exact superpose eq1799 eq14
    | exact resolve eq14 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1838 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1814 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1814
    | exact resolve eq1814 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1927 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1258 y
       have i₂ := eq1838 y
       grind)
    | exact superpose eq1838 eq1258
    | (have j0 := eq1258 y
       grind)
    | (have r₁ := eq1258 y
       have r₂ := eq1838 y
       grind)
    | exact resolve eq1258 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq1838
  have eq1943 : y = (M.op y y) := by grind
  clear eq1927
  have eq2067 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq1943
       grind)
    | exact superpose eq1943 eq23
    | exact resolve eq23 eq1943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1943
  have eq2474 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1826
       have i₂ := eq2067 x
       grind)
    | exact superpose eq2067 eq1826
    | exact resolve eq1826 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq2067
  have eq2475 : False := by grind
  exact eq2475

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pxx_pxy_Equation455 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) X0
       have i₂ := eq8 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq20
  have eq151 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq33 X0 X1 X2
       grind)
    | exact superpose eq33 eq11
    | exact resolve eq11 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq49 x y
       grind)
    | exact superpose eq49 eq14
    | (have j1 := eq49 x y
       grind)
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq188
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq188 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1325 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1324
  have eq1328 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq8
    | exact resolve eq8 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1342 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1328 X0
       have i₂ := eq23 (σ x) (σ y)
       grind)
    | exact superpose eq23 eq1328
    | exact resolve eq1328 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328
  have eq2771 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq151 X0 x x
       have i₂ := eq33 X0 x x
       grind)
    | exact superpose eq33 eq151
    | exact resolve eq151 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq151
  have eq2780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2771 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2771 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq2771 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2882 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq2780 (σ X0)
       grind)
    | exact superpose eq2780 eq13
    | exact resolve eq13 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2886 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0 X0
       have i₂ := eq2780 (τ X0)
       grind)
    | exact superpose eq2780 eq75
    | exact resolve eq75 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2889 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2886 X0
       have i₂ := eq2780 X0
       grind)
    | exact superpose eq2780 eq2886
    | exact resolve eq2886 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886
  have eq2893 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2882 X0
       have i₂ := eq2780 X0
       grind)
    | exact superpose eq2780 eq2882
    | exact resolve eq2882 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2780 eq2882
  have eq3173 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq2889 X0
       grind)
    | exact superpose eq2889 eq23
    | exact resolve eq23 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889
  have eq3397 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3173 (σ y) X0
       have i₂ := eq1342 (σ y)
       grind)
    | exact superpose eq1342 eq3173
    | exact resolve eq3173 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342 eq3173
  have eq3498 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3397 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq3397
    | exact resolve eq3397 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3397
  have eq3936 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq2893 X0
       grind)
    | exact superpose eq2893 eq23
    | exact resolve eq23 eq2893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2893
  have eq6950 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq3498 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3498
  have eq6951 : x = (M.op x y) := by grind
  clear eq6950
  have eq7208 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq6951
       grind)
    | exact superpose eq6951 eq8
    | exact resolve eq8 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951
  have eq7242 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq7208 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq7208
    | exact resolve eq7208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq7208
  have eq7658 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3936 y X0
       have i₂ := eq7242 y
       grind)
    | exact superpose eq7242 eq3936
    | exact resolve eq3936 eq7242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq8652 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq7658 (σ x)
       grind)
    | exact superpose eq7658 eq14
    | exact resolve eq14 eq7658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7658
  have eq8657 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq8652
       have i₂ := eq7242 x
       grind)
    | exact superpose eq7242 eq8652
    | exact resolve eq8652 eq7242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7242 eq8652
  have eq8658 : False := by grind
  exact eq8658

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_x_pyy_pxy_Equation455 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law455 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (M.op X0 X0) X0
       have i₂ := eq8 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = (M.op (M.op X1 (M.op X2 (M.op X2 X1))) (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq11
    | (have j0 := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       grind)
    | (have r₁ := eq11 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq11 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X1 X1)
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq11
    | (have j0 := eq11 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq11 X1 (M.op X0 X0)
       have r₂ := eq23 X0 X1
       grind)
    | exact resolve eq11 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = (M.op (M.op X1 (M.op X2 (M.op X2 X1))) (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq23 X1 (M.op X1 X1)
       grind)
    | exact superpose eq23 eq32
    | exact resolve eq32 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 X1))) = (k X0 (M.op X1 (M.op X2 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1 X2
       have i₂ := eq8 (M.op X1 (M.op X2 (M.op X2 X1))) X1 X2
       grind)
    | exact superpose eq8 eq33
    | exact resolve eq33 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq20
  have eq93 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 (M.op X1 X0)))) = (k X2 (σ (M.op X0 (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have i₂ := eq35 (τ X2) X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq102 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X1 (M.op X0 X0)
       have i₂ := eq34 (σ X1) X0
       grind)
    | exact superpose eq34 eq50
    | exact resolve eq50 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq41 x y
       grind)
    | exact superpose eq41 eq14
    | (have j1 := eq41 x y
       grind)
    | exact resolve eq14 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq11 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ (k X0 X0)) = (k X1 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (σ X1)
       have i₂ := eq41 X1 X1
       grind)
    | exact superpose eq41 eq34
    | (have j1 := eq41 X0 X0
       grind)
    | exact resolve eq34 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq126 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq127 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq122 X0 X1
       have j1 := eq11 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq122 X0 X1
       have r₂ := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq130 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq127
    | (have j0 := eq127 X0 X1
       grind)
    | exact resolve eq127 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq337 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (τ X0) (τ X1)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq126
    | (have j0 := eq126 (τ X0) (τ X1)
       grind)
    | exact resolve eq126 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq344 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq337
    | (have j0 := eq337 X0 X1
       grind)
    | exact resolve eq337 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq348 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq351 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq352 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq523 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq119
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq119 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq524 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq523
  have eq530 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ y) (σ x)
       have i₂ := eq524
       grind)
    | exact superpose eq524 eq8
    | exact resolve eq8 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq532 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq530 X0
       have i₂ := eq23 (σ x) (σ y)
       grind)
    | exact superpose eq23 eq530
    | exact resolve eq530 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq546 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (τ X1) (τ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq130
    | exact resolve eq130 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq130
  have eq553 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq556 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq559 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq556
    | (have j0 := eq556 X0 X1
       grind)
    | exact resolve eq556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq560 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq559
    | (have j0 := eq559 X0 X1
       grind)
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq564 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq102 (σ y) x
       have i₂ := eq532 (σ y)
       grind)
    | exact superpose eq532 eq102
    | exact resolve eq102 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq532
  have eq577 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq564
    | exact resolve eq564 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq634 : ∀ X0 : G, y ≠ X0 ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq352 X0 y
       have i₂ := eq577 X0
       grind)
    | exact superpose eq577 eq352
    | (have j0 := eq352 X0 y
       grind)
    | (have r₁ := eq352 y y
       have r₂ := eq577 y
       grind)
    | exact resolve eq352 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq577
  have eq1385 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq634 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq1470 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq1385
       grind)
    | exact superpose eq1385 eq23
    | exact resolve eq23 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1550 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq1470 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1551 : x = (M.op x y) := by grind
  clear eq1550
  have eq1628 : ∀ X0 : G, (σ (M.op y (M.op x x))) = (k X0 (σ (M.op y (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq93 y x x
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq93
    | exact resolve eq93 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq1629 : ∀ X0 : G, (M.op y (M.op x x)) = (k X0 (M.op y (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 y x
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq35
    | exact resolve eq35 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1632 : ∀ X0 : G, (M.op X0 (M.op y (M.op x x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq8 X0 y x
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq8
    | exact resolve eq8 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1634 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1632 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq1632
    | exact resolve eq1632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1635 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1629 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq1629
    | exact resolve eq1629 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq1636 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1628 X0
       have i₂ := eq23 x y
       grind)
    | exact superpose eq23 eq1628
    | exact resolve eq1628 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1960 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq560 X0 (σ y)
       have i₂ := eq1636 X0
       grind)
    | exact superpose eq1636 eq560
    | (have r₁ := eq560 (σ y) (σ y)
       have r₂ := eq1636 (σ y)
       grind)
    | exact resolve eq560 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq1636
  have eq2601 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq124 y x
       have i₂ := eq1635 y
       grind)
    | exact superpose eq1635 eq124
    | (have j0 := eq124 y x
       grind)
    | exact resolve eq124 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1635
  have eq2673 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq2601 x
       have r₂ := eq1960 (k x (σ y))
       grind)
    | (have r₁ := eq2601 x
       have r₂ := eq1960 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq2601 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960 eq2601
  have eq2689 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (σ y) X0
       have i₂ := eq2673
       grind)
    | exact superpose eq2673 eq23
    | exact resolve eq23 eq2673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2673
  have eq2787 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2689 (σ x)
       grind)
    | exact superpose eq2689 eq14
    | exact resolve eq14 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689
  have eq2789 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2787
       have i₂ := eq1634 x
       grind)
    | exact superpose eq1634 eq2787
    | exact resolve eq2787 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634 eq2787
  have eq2790 : False := by grind
  exact eq2790

/-- `Equation508`: `x = y ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_x_pxx_pyx_Equation508 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law508 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law508.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 (M.op X2 X2)) X1 (M.op X0 (M.op X2 X2))
       have i₂ := eq8 X0 (M.op X0 (M.op X2 X2)) X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X1 (M.op X0 X0)
       have i₂ := eq8 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 X1 x
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (M.op X1 X1) X0 X1
       have i₂ := eq22 (M.op X1 X1) X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X0) X1
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq11
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq27 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X1
       have r₂ := eq27 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq111 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq118 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X0 X0) X1
       have i₂ := eq31 X0 (σ X1)
       grind)
    | exact superpose eq31 eq20
    | exact resolve eq20 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq130 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X0
       have i₂ := eq27 (σ X0) X1
       grind)
    | (have i₁ := eq45 X0 X0
       have i₂ := eq27 X0 (σ X0)
       grind)
    | exact superpose eq27 eq45
    | exact resolve eq45 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 (σ X0)
       have i₂ := eq45 X2 X0
       grind)
    | exact superpose eq45 eq27
    | (have j1 := eq45 X2 X0
       grind)
    | exact resolve eq27 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45
  have eq464 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq519 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq963 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq130 X1 (M.op X0 X0)
       have i₂ := eq31 X0 (M.op X0 X0)
       grind)
    | exact superpose eq31 eq130
    | (have j0 := eq130 X1 (M.op X0 X0)
       grind)
    | exact resolve eq130 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1002 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq130 X0 (τ X1)
       grind)
    | exact superpose eq130 eq16
    | (have j1 := eq130 X0 (τ X1)
       grind)
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq130
  have eq1028 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq963 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1038 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1002 X0 X1
       have j1 := eq68 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq1002 X0 X1
       have r₂ := eq68 X0 (k (σ (τ X1)) X1) x
       grind)
    | (have r₁ := eq1002 X0 X1
       have r₂ := eq68 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq1002 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1002
  have eq1057 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1038 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1038
    | exact resolve eq1038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1164 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 X1
       have i₂ := eq1057 X1 X0
       grind)
    | exact superpose eq1057 eq23
    | exact resolve eq23 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1057
  have eq1544 : ∀ X0 X1 : G, (M.op X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1164 (τ X0) X1
       have i₂ := eq111 X0 X0
       grind)
    | exact superpose eq111 eq1164
    | exact resolve eq1164 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1545 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1164 (τ (M.op X0 X0)) X1
       have i₂ := eq118 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq118 eq1164
    | exact resolve eq1164 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq6132 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1028 X0 X1
       have i₂ := eq519 X2 X0
       grind)
    | exact superpose eq519 eq1028
    | (have j1 := eq519 X2 X0
       grind)
    | exact resolve eq1028 eq519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq1028
  have eq15327 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq149 y X0 x
       grind)
    | exact superpose eq149 eq14
    | (have j1 := eq149 y X0 x
       grind)
    | exact resolve eq14 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq15423 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq15327 X0
       have j1 := eq6132 y X0 x
       grind)
    | (have r₁ := eq15327 X0
       have r₂ := eq6132 y x x
       grind)
    | exact resolve eq15327 eq6132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6132 eq15327
  have eq15585 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1545 x X0
       have i₂ := eq15423 x
       grind)
    | exact superpose eq15423 eq1545
    | exact resolve eq1545 eq15423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1545
  have eq15621 : ∀ X0 : G, (σ y) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1544 X0 (τ (k X0 X0))
       have i₂ := eq15423 (τ (k X0 X0))
       grind)
    | exact superpose eq15423 eq1544
    | exact resolve eq1544 eq15423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq15622 : ∀ X0 : G, (σ y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1164 X0 (k X0 X0)
       have i₂ := eq15423 (k X0 X0)
       grind)
    | exact superpose eq15423 eq1164
    | exact resolve eq1164 eq15423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164 eq15423
  have eq15648 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq15621 x
       have i₂ := eq15622 x
       grind)
    | exact superpose eq15622 eq15621
    | exact resolve eq15621 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15621 eq15622
  have eq15671 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq15585 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq15585
    | exact resolve eq15585 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15585
  have eq15714 : y = (σ y) := by
    first
    | (have i₁ := eq15648
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq15648
    | exact resolve eq15648 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648
  have eq15768 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq15714
       grind)
    | exact superpose eq15714 eq14
    | exact resolve eq14 eq15714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15714
  have eq15821 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq15768
       have i₂ := eq15671 (σ x)
       grind)
    | exact superpose eq15671 eq15768
    | exact resolve eq15768 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15768
  have eq15835 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15821
       have i₂ := eq15671 x
       grind)
    | exact superpose eq15671 eq15821
    | exact resolve eq15821 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671 eq15821
  have eq15836 : False := by grind
  exact eq15836
