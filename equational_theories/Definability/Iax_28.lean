import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4447`: `x ◇ (y ◇ x) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pxy_Equation4447 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4447 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4447.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
    intro X0 X1 X2
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X3) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X1) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq8 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 (M.op X3 X3))
       have i₂ := eq8 (M.op X3 X3) X0 X1
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq44 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq117 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 (M.op X3 (M.op X1 X1))
       have i₂ := eq22 (M.op X1 X1) X3 X2
       grind)
    | (have i₁ := eq8 X0 X1 (M.op X3 (M.op X1 X1))
       have i₂ := eq22 X2 X3 (M.op X1 X1)
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq153 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X2) X3) = (M.op X4 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X2 X3 X4 (M.op X1 X1)
       have i₂ := eq8 X0 X1 X4
       grind)
    | (have i₁ := eq23 X0 X1 (M.op X1 X0) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq204 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq37 X1 (σ X0) X2
       grind)
    | exact superpose eq37 eq44
    | (have j1 := eq37 X1 X1 X2
       grind)
    | exact resolve eq44 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq212 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq37 X1 X2 (τ X0)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 X1 X2 X2
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq37
  have eq218 : ∀ X0 X1 X2 : G, (k X0 (τ X1)) = X0 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq204
    | (have j0 := eq204 X0 X1 X2
       grind)
    | exact resolve eq204 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1426 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq35 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2962 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op X5 (M.op X6 (M.op X3 X6))) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq18 X6 X3 X5 x
       have i₂ := eq153 X1 X2 (M.op X3 X3) x X0
       grind)
    | (have i₁ := eq18 X0 X1 X2 (M.op X0 (M.op X1 X0))
       have i₂ := eq153 X0 X1 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact superpose eq153 eq18
    | exact resolve eq18 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq153
  have eq11584 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (τ (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq218 X2 (σ X1) (σ X0)
       grind)
    | exact superpose eq218 eq13
    | (have j1 := eq218 X2 (σ X1) X2
       grind)
    | exact resolve eq13 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq11600 : ∀ X0 X1 X2 : G, (k X2 X1) = X2 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11584 X0 X1 X2
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq11584
    | (have j0 := eq11584 X0 X1 X2
       grind)
    | exact resolve eq11584 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11584
  have eq14357 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 (σ X0) X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq212
    | (have j0 := eq212 X0 X1 X2
       grind)
    | exact resolve eq212 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq14474 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14357 X0 X1 X2
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq14357
    | (have j0 := eq14357 X0 X1 X2
       grind)
    | exact resolve eq14357 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14357
  have eq22509 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1426 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1426
    | (have j0 := eq1426 (τ X0)
       grind)
    | exact resolve eq1426 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq22547 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq22509 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22509
    | (have j0 := eq22509 X0
       grind)
    | exact resolve eq22509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509
  have eq22562 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22547 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22547
    | (have j0 := eq22547 X0
       grind)
    | exact resolve eq22547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22547
  have eq362281 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq11600 x y X0
       grind)
    | exact superpose eq11600 eq14
    | (have j1 := eq11600 X0 y X0
       grind)
    | exact resolve eq14 eq11600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11600
  have eq362340 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq362281 X0
       have j1 := eq14474 X0 y X0
       grind)
    | (have r₁ := eq362281 X0
       have r₂ := eq14474 x y x
       grind)
    | exact resolve eq362281 eq14474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14474 eq362281
  have eq362657 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1426 y
       have i₂ := eq362340 y
       grind)
    | exact superpose eq362340 eq1426
    | (have j0 := eq1426 y
       grind)
    | exact resolve eq1426 eq362340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq362661 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22562 y
       have i₂ := eq362340 y
       grind)
    | exact superpose eq362340 eq22562
    | (have j0 := eq22562 y
       grind)
    | (have r₁ := eq22562 y
       have r₂ := eq362340 y
       grind)
    | exact resolve eq22562 eq362340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22562 eq362340
  have eq362727 : y = (M.op y y) := by grind
  clear eq362661
  have eq362731 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq362657
  have eq366350 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 y y x
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq8
    | exact resolve eq8 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366369 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 X1 y y
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq117
    | exact resolve eq117 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366584 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq366369 X0 X1
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq366369
    | exact resolve eq366369 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366369
  have eq366592 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq366350 X0
       have i₂ := eq362727
       grind)
    | exact superpose eq362727 eq366350
    | exact resolve eq366350 eq362727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362727 eq366350
  have eq375192 : ∀ X0 X1 X2 : G, y = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2962 X0 X1 X2 x y x
       have i₂ := eq366592 (M.op x (M.op x x))
       grind)
    | exact superpose eq366592 eq2962
    | exact resolve eq2962 eq366592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962 eq366592
  have eq375241 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq375192 X0 x x
       have i₂ := eq366584 x x
       grind)
    | exact superpose eq366584 eq375192
    | exact resolve eq375192 eq366584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375192
  have eq415304 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 X0 X1 (σ y) (σ y)
       have i₂ := eq362731
       grind)
    | exact superpose eq362731 eq117
    | exact resolve eq117 eq362731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq415484 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq415304 X0 X1
       have i₂ := eq362731
       grind)
    | exact superpose eq362731 eq415304
    | exact resolve eq415304 eq362731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362731 eq415304
  have eq415648 : y = (σ y) := by
    first
    | (have i₁ := eq415484 x x
       have i₂ := eq366584 x x
       grind)
    | exact superpose eq366584 eq415484
    | exact resolve eq415484 eq366584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366584 eq415484
  have eq415745 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq415648
       grind)
    | exact superpose eq415648 eq14
    | exact resolve eq14 eq415648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415811 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq415745
       have i₂ := eq375241 (σ x)
       grind)
    | exact superpose eq375241 eq415745
    | exact resolve eq415745 eq375241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415745
  have eq415832 : y ≠ (σ y) := by
    first
    | (have i₁ := eq415811
       have i₂ := eq375241 x
       grind)
    | exact superpose eq375241 eq415811
    | exact resolve eq415811 eq375241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375241 eq415811
  have eq415837 : False := by grind
  exact eq415837

/-- `Equation4448`: `x ◇ (y ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4448 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4448 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4448.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
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
  have eq18 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X2)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X2 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X0 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 X2 (M.op X0 X2)
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X3) X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X3) X0
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq28 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24
    | exact resolve eq24 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq34 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq55 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X2 X3 X4 (M.op X0 X2)
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq20
    | exact resolve eq20 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X2) (M.op (M.op X0 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    grind
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq97 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq28 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq28
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq28 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq144 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op X2 X3) X3 X4
       have i₂ := eq21 X0 X1 X2 X3
       grind)
    | exact superpose eq21 eq8
    | exact resolve eq8 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X2 X3) X1 X0 X4
       have i₂ := eq21 X2 X3 X1 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq159 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq42
  have eq173 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq159 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq159
    | exact resolve eq159 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq242 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 (M.op X1 X2) X0
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq92
    | (have j0 := eq92 (M.op X1 X2) X0
       grind)
    | (have r₁ := eq92 (M.op X0 (M.op X0 X0)) X0
       have r₂ := eq8 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq92 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X4) (M.op (M.op X1 X3) X2)) = (M.op (M.op (M.op X1 X3) X2) (M.op (M.op X0 (M.op X1 X0)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 (M.op (M.op X1 X3) X2) X2 X4
       have i₂ := eq22 X0 X1 X2 X3
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq173 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq173 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq173
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq173 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X1) X1 x
       have i₂ := eq18 X0 X2 X1 x
       grind)
    | exact superpose eq18 eq8
    | exact resolve eq8 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X2 X4)) (M.op (M.op X2 X3) X0)) = (M.op (M.op (M.op X2 X3) X0) (M.op (M.op X0 X1) (M.op X2 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X4 X2 (M.op (M.op X2 X3) X0) X0
       have i₂ := eq18 X2 X3 X0 X1
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1003 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X4 X5) X0) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq55 x x X4 X5 X0
       have i₂ := eq148 X0 X1 x x X4
       grind)
    | exact superpose eq148 eq55
    | exact resolve eq55 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1005 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 x x X1 X0
       have i₂ := eq148 X0 X2 x x X1
       grind)
    | exact superpose eq148 eq21
    | exact resolve eq21 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq148
  have eq1131 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X2 X3 X4
       have i₂ := eq1003 X2 X3 X0 X1
       grind)
    | exact superpose eq1003 eq8
    | exact resolve eq8 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X5 (M.op X3 X5)) X2) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq22 X5 X3 X2 x
       have i₂ := eq1003 X2 (M.op X3 x) X0 X1
       grind)
    | exact superpose eq1003 eq22
    | exact resolve eq22 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1156 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ X2 ∨ (k X2 (M.op X3 X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X2 (M.op X3 X2)
       have i₂ := eq1003 X2 X3 X0 X1
       grind)
    | exact superpose eq1003 eq92
    | (have j0 := eq92 X2 (M.op X3 X2)
       grind)
    | (have r₁ := eq92 (M.op X0 (M.op X1 X0)) X0
       have r₂ := eq1003 X0 X1 X0 (M.op X1 X0)
       grind)
    | exact resolve eq92 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1219 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq34 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq34
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1233 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq34 x y
       grind)
    | exact superpose eq34 eq14
    | (have j1 := eq34 x y
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1261 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | (have j1 := eq34 X0 X1
       grind)
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq173 X1
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq173
    | (have j1 := eq34 X1 X0
       grind)
    | exact resolve eq173 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1296 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1300 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1271 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq1271
    | (have j0 := eq1271 X0 X1
       grind)
    | exact resolve eq1271 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1883 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (k (M.op X2 X3) (M.op (M.op X0 X1) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    grind
  have eq6850 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6974 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq10
    | (have j1 := eq37 X0 X1
       grind)
    | exact resolve eq10 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq7002 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6850 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq6850
    | (have j0 := eq6850 X0 X1
       grind)
    | exact resolve eq6850 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6850
  have eq9254 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq14
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq14 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9261 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq86 X0 X0
       grind)
    | exact superpose eq86 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq86 X0 X0
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq11734 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq97
    | (have j0 := eq97 X1 (σ X0)
       grind)
    | exact resolve eq97 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq11795 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11734 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq11734
    | (have j0 := eq11734 X0 X1
       grind)
    | exact resolve eq11734 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11734
  have eq13154 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1296 X0
       have i₂ := eq11795 X0 X0
       grind)
    | exact superpose eq11795 eq1296
    | (have j0 := eq1296 X0
       have j1 := eq11795 X0 X0
       grind)
    | (have r₁ := eq1296 x
       have r₂ := eq11795 x x
       grind)
    | exact resolve eq1296 eq11795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13181 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13154 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13154
  have eq15916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1233
       have i₂ := eq7002 y x
       grind)
    | exact superpose eq7002 eq1233
    | (have j1 := eq7002 (σ y) (σ x)
       grind)
    | (have r₁ := eq1233
       have r₂ := eq7002 y x
       grind)
    | exact resolve eq1233 eq7002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq15917 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq15916
  have eq15928 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq173 x
       have i₂ := eq15917
       grind)
    | exact superpose eq15917 eq173
    | exact resolve eq173 eq15917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq16007 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15928
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq15928
    | exact resolve eq15928 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15928
  have eq16101 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq16007
       grind)
    | exact superpose eq16007 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq16007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16104 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq7002 y x
       have i₂ := eq16007
       grind)
    | exact superpose eq16007 eq7002
    | (have j0 := eq7002 y x
       grind)
    | exact resolve eq7002 eq16007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7002 eq16007
  have eq16105 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq16104
  have eq16106 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq16101
  have eq16796 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1 x y
       have i₂ := eq16106
       grind)
    | exact superpose eq16106 eq1003
    | exact resolve eq1003 eq16106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16800 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1131 X0 X1 X2 x y
       have i₂ := eq16106
       grind)
    | exact superpose eq16106 eq1131
    | exact resolve eq1131 eq16106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16802 : ∀ X0 X1 : G, (M.op x X0) ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 x y X0 X1
       have i₂ := eq16106
       grind)
    | exact superpose eq16106 eq1156
    | (have j0 := eq1156 X0 X1 X0 X1
       grind)
    | exact resolve eq1156 eq16106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq22373 : x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16796 y x
       have i₂ := eq16106
       grind)
    | exact superpose eq16106 eq16796
    | exact resolve eq16796 eq16106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16106
  have eq22632 : x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq22373
  have eq23597 : ∀ X0 : G, x = (k x (M.op (M.op y X0) x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq73 y x x
       have i₂ := eq22632
       grind)
    | exact superpose eq22632 eq73
    | exact resolve eq73 eq22632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq23650 : x = (k x (M.op x (M.op y x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23597 x
       have i₂ := eq8 x y x
       grind)
    | exact superpose eq8 eq23597
    | exact resolve eq23597 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23597
  have eq39556 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op X2 X3) (M.op (M.op X0 X4) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1131 X2 X3 (M.op (M.op X0 X4) X1) X0 X1
       have i₂ := eq816 X0 X1 X4
       grind)
    | exact superpose eq816 eq1131
    | exact resolve eq1131 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq49748 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) X1
       have i₂ := eq423 (σ X1) X0
       grind)
    | exact superpose eq423 eq27
    | (have j1 := eq423 (σ X1) X0
       grind)
    | exact resolve eq27 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq423
  have eq49778 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49748 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq49748
    | (have j0 := eq49748 X0 X1
       grind)
    | exact resolve eq49748 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49748
  have eq49814 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49778 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq49778
    | (have j0 := eq49778 X0 X1
       grind)
    | exact resolve eq49778 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49778
  have eq138026 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X4) (M.op X2 X2)) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) (M.op (M.op X3 (M.op (M.op X0 X1) X3)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq144 X0 X1 X2 X2 X4
       have i₂ := eq297 X3 (M.op X0 X1) X2 X2 X2
       grind)
    | (have i₁ := eq144 X0 X1 (M.op X1 (M.op X0 X1)) X2 X4
       have i₂ := eq297 (M.op X0 X1) X1 X2 (M.op X0 X1) X4
       grind)
    | exact superpose eq297 eq144
    | exact resolve eq144 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq297
  have eq138983 : ∀ X2 X3 X4 : G, (M.op (M.op X3 X2) (M.op X2 (M.op X3 X2))) = (M.op (M.op X2 X4) (M.op X2 X2)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq138026 x x X2 X3 X4
       have i₂ := eq39556 X3 X2 (M.op (M.op x x) X2) X2 (M.op (M.op x x) X3)
       grind)
    | exact superpose eq39556 eq138026
    | exact resolve eq138026 eq39556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39556 eq138026
  have eq139110 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49814 x x
       have i₂ := eq15917
       grind)
    | exact superpose eq15917 eq49814
    | (have j0 := eq49814 x x
       grind)
    | exact resolve eq49814 eq15917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49814
  have eq139192 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq139110
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq139110
    | exact resolve eq139110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139110
  have eq156432 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq139192
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq139192
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq139192 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139192
  have eq156495 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq156432
  have eq157212 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq92 x x
       have i₂ := eq156495
       grind)
    | exact superpose eq156495 eq92
    | (have j0 := eq92 x x
       grind)
    | (have r₁ := eq92 x x
       have r₂ := eq156495
       grind)
    | exact resolve eq92 eq156495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157352 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1 x x
       have i₂ := eq156495
       grind)
    | exact superpose eq156495 eq1003
    | exact resolve eq1003 eq156495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156495
  have eq157399 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq92 x x
       grind)
    | (have r₁ := eq157212
       have r₂ := eq92 x x
       grind)
    | exact resolve eq157212 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq157212
  have eq162252 : x = (k x (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23650
       have i₂ := eq157352 x y
       grind)
    | exact superpose eq157352 eq23650
    | exact resolve eq23650 eq157352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23650 eq157352
  have eq162261 : x = (k x (M.op y x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq16802 x y
       grind)
    | (have r₁ := eq162252
       have r₂ := eq16802 x x
       grind)
    | exact resolve eq162252 eq16802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16802 eq162252
  have eq164639 : x = (k x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq162261
       have i₂ := eq22632
       grind)
    | exact superpose eq22632 eq162261
    | exact resolve eq162261 eq22632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22632 eq162261
  have eq164687 : x = (k x x) ∨ y = (M.op x x) := by grind
  clear eq164639
  have eq167109 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1296 x
       have i₂ := eq164687
       grind)
    | exact superpose eq164687 eq1296
    | (have j0 := eq1296 x
       grind)
    | exact resolve eq1296 eq164687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164687
  have eq167136 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq167109
  have eq177824 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15917
       have i₂ := eq167136
       grind)
    | exact superpose eq167136 eq15917
    | exact resolve eq15917 eq167136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178085 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16800 (σ x) (σ x) X0
       have i₂ := eq167136
       grind)
    | exact superpose eq167136 eq16800
    | exact resolve eq16800 eq167136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16800 eq167136
  have eq178092 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq178085 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178085
  have eq178101 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq177824
  have eq193493 : (σ y) = (M.op x (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15917
       have i₂ := eq178092 (σ x)
       grind)
    | exact superpose eq178092 eq15917
    | exact resolve eq15917 eq178092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15917 eq178092
  have eq193998 : (σ y) = (M.op x (σ x)) ∨ y = (M.op x x) := by grind
  clear eq193493
  have eq197217 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16796 (σ x) x
       have i₂ := eq193998
       grind)
    | exact superpose eq193998 eq16796
    | exact resolve eq16796 eq193998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16796 eq193998
  have eq197225 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq197217
  have eq203323 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq197225
       grind)
    | exact superpose eq197225 eq14
    | exact resolve eq14 eq197225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197225
  have eq205746 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq203323
       have i₂ := eq16105
       grind)
    | exact superpose eq16105 eq203323
    | exact resolve eq203323 eq16105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16105 eq203323
  have eq205747 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq205746
  have eq205749 : y = (M.op x x) := by
    first
    | (have r₁ := eq205747
       have r₂ := eq178101
       grind)
    | exact resolve eq205747 eq178101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205747
  have eq209240 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1 x x
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq1003
    | exact resolve eq1003 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq209242 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1005 x X0 x
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq1005
    | exact resolve eq1005 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq209245 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1131 X0 X1 X2 x x
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq1131
    | exact resolve eq1131 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq213240 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq209240 (σ X1) (σ X0)
       have i₂ := eq1300 X1 X0
       grind)
    | exact superpose eq1300 eq209240
    | (have j1 := eq1300 X1 X0
       grind)
    | exact resolve eq209240 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq213271 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq209240 x x
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq209240
    | exact resolve eq209240 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213870 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X3)) (M.op X2 (M.op X0 X1))) = (M.op y (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1137 X0 X1 (M.op X2 (M.op X0 X1)) X4 X3
       have i₂ := eq209240 (M.op X0 X1) X2
       grind)
    | exact superpose eq209240 eq1137
    | exact resolve eq1137 eq209240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq213957 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq213870 X0 X1 X2 x x
       have i₂ := eq209245 x (M.op x x) (M.op X2 (M.op X0 X1))
       grind)
    | exact superpose eq209245 eq213870
    | exact resolve eq213870 eq209245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213870
  have eq220200 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq209240 (M.op X0 x) x
       have i₂ := eq209242 X0
       grind)
    | exact superpose eq209242 eq209240
    | exact resolve eq209240 eq209242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220201 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq220200 X0
       have i₂ := eq209245 X0 x (M.op x y)
       grind)
    | exact superpose eq209245 eq220200
    | exact resolve eq220200 eq209245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220200
  have eq220360 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq220201 X0
       have i₂ := eq209240 y x
       grind)
    | exact superpose eq209240 eq220201
    | exact resolve eq220201 eq209240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220201
  have eq224084 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op y X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq209245 (σ X0) (σ X0) X1
       have i₂ := eq13181 X0
       grind)
    | exact superpose eq13181 eq209245
    | (have j1 := eq13181 X0
       grind)
    | exact resolve eq209245 eq13181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13181
  have eq231016 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1883 x (M.op X0 x) (M.op X0 X1) X2
       have i₂ := eq848 X2 X3 X0 X1 x
       grind)
    | exact superpose eq848 eq1883
    | exact resolve eq1883 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848 eq1883
  have eq232131 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op y (M.op (M.op X2 X3) (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq231016 X0 X1 X2 X3
       have i₂ := eq209245 (M.op X0 X1) X2 (M.op (M.op X2 X3) (M.op X0 X2))
       grind)
    | exact superpose eq209245 eq231016
    | exact resolve eq231016 eq209245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231016
  have eq232250 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op y (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232131 X0 X1 X2 x
       have i₂ := eq213957 X0 X2 (M.op X2 x)
       grind)
    | exact superpose eq213957 eq232131
    | exact resolve eq232131 eq213957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232131
  have eq232367 : ∀ X0 X2 : G, (M.op y X2) = (k (M.op y X2) (M.op y (M.op X0 X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq232250 X0 x X2
       have i₂ := eq209245 X0 x X2
       grind)
    | exact superpose eq209245 eq232250
    | exact resolve eq232250 eq209245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232250
  have eq275854 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq232367 x y
       have i₂ := eq209240 y x
       grind)
    | exact superpose eq209240 eq232367
    | exact resolve eq232367 eq209240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232367
  have eq280661 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq1296 (M.op y y)
       have i₂ := eq275854
       grind)
    | exact superpose eq275854 eq1296
    | (have j0 := eq1296 (M.op y y)
       grind)
    | exact resolve eq1296 eq275854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275854
  have eq280682 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
  clear eq280661
  have eq447583 : ∀ X0 : G, (τ (σ (M.op y y))) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1261 (M.op y y) X0
       have i₂ := eq280682
       grind)
    | exact superpose eq280682 eq1261
    | (have j0 := eq1261 (M.op y y) X0
       grind)
    | exact resolve eq1261 eq280682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq447695 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq209245 (σ (M.op y y)) (σ (M.op y y)) X0
       have i₂ := eq280682
       grind)
    | exact superpose eq280682 eq209245
    | exact resolve eq209245 eq280682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447745 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (M.op (σ (M.op y y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq447583 X0
       have i₂ := eq9 (M.op y y)
       grind)
    | exact superpose eq9 eq447583
    | (have j0 := eq447583 X0
       grind)
    | exact resolve eq447583 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447583
  have eq447758 : ∀ X0 : G, (M.op y (σ X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq447745 X0
       have i₂ := eq447695 (σ X0)
       grind)
    | exact superpose eq447695 eq447745
    | (have j0 := eq447745 X0
       grind)
    | exact resolve eq447745 eq447695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447745
  have eq449645 : (σ (M.op y y)) = (M.op y (σ (M.op y y))) := by
    first
    | (have i₁ := eq280682
       have i₂ := eq447695 (σ (M.op y y))
       grind)
    | exact superpose eq447695 eq280682
    | exact resolve eq280682 eq447695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280682 eq447695
  have eq609192 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6974 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6974
    | (have j0 := eq6974 X1 (σ X0)
       grind)
    | exact resolve eq6974 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609221 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq6974 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6974
  have eq609222 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq609221 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq609221
    | (have j0 := eq609221 X0
       grind)
    | exact resolve eq609221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609221
  have eq609238 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq609192 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq609192
    | (have j0 := eq609192 X0 X1
       grind)
    | exact resolve eq609192 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609192
  have eq609255 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq609222 (σ X0)
       have i₂ := eq13 X0 X0
       grind)
    | exact superpose eq13 eq609222
    | (have j0 := eq609222 (σ X0)
       grind)
    | exact resolve eq609222 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609222
  have eq609293 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq609255 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq609255
    | (have j0 := eq609255 X0
       grind)
    | exact resolve eq609255 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609255
  have eq610094 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq609293 X0
       have i₂ := eq11795 X0 X0
       grind)
    | exact superpose eq11795 eq609293
    | (have j0 := eq609293 X0
       have j1 := eq11795 X0 X0
       grind)
    | (have r₁ := eq609293 x
       have r₂ := eq11795 x x
       grind)
    | exact resolve eq609293 eq11795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11795 eq609293
  have eq610100 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq610094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610094
  have eq610405 : (σ x) = (σ y) ∨ y = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq610100 x
       have i₂ := eq178101
       grind)
    | exact superpose eq178101 eq610100
    | exact resolve eq610100 eq178101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178101 eq610100
  have eq610432 : y = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq610405
  have eq616234 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2))) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138983 X0 x X0
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq138983 X2 x x
       have i₂ := eq12 X0 (M.op X2 x)
       grind)
    | exact superpose eq12 eq138983
    | (have j1 := eq12 X0 (M.op (M.op X1 X2) (M.op X2 (M.op X1 X2)))
       grind)
    | exact resolve eq138983 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138983
  have eq616753 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op y (M.op X2 (M.op X1 X2))) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq616234 X0 X1 X2
       have i₂ := eq209245 X1 X2 (M.op X2 (M.op X1 X2))
       grind)
    | exact superpose eq209245 eq616234
    | (have j0 := eq616234 X0 X1 X2
       grind)
    | exact resolve eq616234 eq209245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616234
  have eq616922 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op y (M.op X1 X2)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq616753 X0 X1 X2
       have i₂ := eq213957 X1 X2 X2
       grind)
    | exact superpose eq213957 eq616753
    | (have j0 := eq616753 X0 X1 X2
       grind)
    | exact resolve eq616753 eq213957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213957 eq616753
  have eq617820 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x y) ∨ (M.op X0 X1) = (k (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq242 x X0 X1
       have i₂ := eq209242 X0
       grind)
    | exact superpose eq209242 eq242
    | (have j0 := eq242 x X0 X1
       grind)
    | (have r₁ := eq242 x x y
       have r₂ := eq209242 x
       grind)
    | exact resolve eq242 eq209242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209242
  have eq617847 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq242 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq617848 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
    intro X0
    first
    | (have i₁ := eq617847 x
       have i₂ := eq209240 x x
       grind)
    | exact superpose eq209240 eq617847
    | exact resolve eq617847 eq209240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617847
  have eq617919 : ∀ X0 : G, (M.op y y) = (k (M.op y y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq617848 (M.op x y)
       have i₂ := eq209240 y x
       grind)
    | exact superpose eq209240 eq617848
    | exact resolve eq617848 eq209240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617848
  have eq631803 : (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq224084 x (σ y)
       grind)
    | exact superpose eq224084 eq14
    | (have j1 := eq224084 x x
       grind)
    | exact resolve eq14 eq224084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224084
  have eq631961 : (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq631803
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq631803
    | exact resolve eq631803 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631803
  have eq677083 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq220360 x
       have i₂ := eq616922 X0 x x
       grind)
    | exact superpose eq616922 eq220360
    | (have j1 := eq616922 X0 x x
       grind)
    | exact resolve eq220360 eq616922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220360 eq616922
  have eq677733 : ∀ X0 : G, y = (k y (M.op X0 X0)) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    grind
  clear eq677083
  have eq679835 : y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq677733 x
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq677733
    | exact resolve eq677733 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677733
  have eq679915 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq609238 y y
       have i₂ := eq679835
       grind)
    | exact superpose eq679835 eq609238
    | (have j0 := eq609238 y y
       grind)
    | exact resolve eq609238 eq679835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609238 eq679835
  have eq679916 : (σ y) = (σ (M.op y y)) ∨ y = (k x x) := by grind
  clear eq679915
  have eq680075 : (σ y) = (M.op y (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq449645
       have i₂ := eq679916
       grind)
    | exact superpose eq679916 eq449645
    | exact resolve eq449645 eq679916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449645 eq679916
  have eq684225 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq9261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9261
  have eq684226 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq684225 X0 X1
       have j1 := eq1219 X1 X0
       grind)
    | (have r₁ := eq684225 (k X1 X1) X0
       have r₂ := eq1219 X0 X1
       grind)
    | (have r₁ := eq684225 X0 (σ (k X1 X1))
       have r₂ := eq1219 (σ X0) X1
       grind)
    | (have r₁ := eq684225 X1 X0
       have r₂ := eq1219 X0 X1
       grind)
    | exact resolve eq684225 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq684225
  have eq684255 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq684226 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq684226 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq684226 eq16
    | (have j1 := eq684226 (τ X1) X0
       grind)
    | exact resolve eq16 eq684226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq684226
  have eq684274 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq684255 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq684255
    | (have j0 := eq684255 X0 X1
       grind)
    | exact resolve eq684255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684255
  have eq684281 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq684274 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq684274
    | (have j0 := eq684274 X0 X1
       grind)
    | exact resolve eq684274 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684274
  have eq684513 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq684281 (τ X1) X0
       grind)
    | exact superpose eq684281 eq17
    | (have j1 := eq684281 (τ X1) X0
       grind)
    | exact resolve eq17 eq684281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq684556 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq9254
       have i₂ := eq684281 y x
       grind)
    | exact superpose eq684281 eq9254
    | (have j1 := eq684281 y x
       grind)
    | exact resolve eq9254 eq684281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9254 eq684281
  have eq684718 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by grind
  clear eq684556
  have eq684993 : (σ x) ≠ (M.op y (σ y)) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq631961
       have i₂ := eq684718
       grind)
    | exact superpose eq684718 eq631961
    | exact resolve eq631961 eq684718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631961 eq684718
  have eq685007 : (σ x) ≠ (M.op y (σ y)) ∨ y = (k x x) := by grind
  clear eq684993
  have eq685207 : (σ x) ≠ (σ y) ∨ y = (k x x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq685007
       have i₂ := eq680075
       grind)
    | exact superpose eq680075 eq685007
    | exact resolve eq685007 eq680075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680075 eq685007
  have eq685213 : (σ x) ≠ (σ y) ∨ y = (k x x) := by grind
  clear eq685207
  have eq685217 : y = (k x x) := by
    first
    | (have r₁ := eq685213
       have r₂ := eq610432
       grind)
    | exact resolve eq685213 eq610432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610432 eq685213
  have eq685323 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1296 x
       have i₂ := eq685217
       grind)
    | exact superpose eq685217 eq1296
    | (have j0 := eq1296 x
       grind)
    | exact resolve eq1296 eq685217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296
  have eq702330 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq684513 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq684513
    | exact resolve eq684513 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684513
  have eq702374 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq702330 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq702330
    | (have j0 := eq702330 X0 X1
       grind)
    | exact resolve eq702330 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702330
  have eq702929 : ∀ X0 : G, (M.op y y) = X0 ∨ (σ (k (M.op y y) X0)) = (σ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq617919 y
       have i₂ := eq702374 X0 (M.op y y)
       grind)
    | (have i₁ := eq617919 X0
       have i₂ := eq702374 (k (M.op y y) (M.op X0 y)) x
       grind)
    | exact superpose eq702374 eq617919
    | (have j1 := eq702374 X0 (M.op y y)
       grind)
    | exact resolve eq617919 eq702374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617919 eq702374
  have eq702943 : ∀ X0 : G, (σ (M.op y X0)) = (σ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq702929 X0
       have i₂ := eq209245 y y X0
       grind)
    | exact superpose eq209245 eq702929
    | (have j0 := eq702929 X0
       grind)
    | exact resolve eq702929 eq209245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209245 eq702929
  have eq729007 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq702943 X0
       have i₂ := eq447758 X0
       grind)
    | exact superpose eq447758 eq702943
    | (have j0 := eq702943 X0
       have j1 := eq447758 X0
       grind)
    | exact resolve eq702943 eq447758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447758 eq702943
  have eq729010 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq729007 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729007
  have eq729025 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq729010 x
       have i₂ := eq213271
       grind)
    | exact superpose eq213271 eq729010
    | (have j0 := eq729010 x
       grind)
    | exact resolve eq729010 eq213271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729010
  have eq763824 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq213240 x x
       have i₂ := eq685217
       grind)
    | exact superpose eq685217 eq213240
    | exact resolve eq213240 eq685217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213240
  have eq763861 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq763824
       grind)
    | exact superpose eq763824 eq14
    | exact resolve eq14 eq763824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763824
  have eq764004 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq763861
       have i₂ := eq729025
       grind)
    | exact superpose eq729025 eq763861
    | (have r₁ := eq763861
       have r₂ := eq729025
       grind)
    | exact resolve eq763861 eq729025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729025 eq763861
  have eq764009 : x = (M.op y y) ∨ x = y := by grind
  clear eq764004
  have eq764455 : x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq209240 y y
       have i₂ := eq764009
       grind)
    | exact superpose eq764009 eq209240
    | exact resolve eq209240 eq764009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209240
  have eq764501 : x ≠ (M.op x y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq617820 y y
       have i₂ := eq764009
       grind)
    | exact superpose eq764009 eq617820
    | exact resolve eq617820 eq764009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617820 eq764009
  have eq764586 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have r₁ := eq764501
       have r₂ := eq157399
       grind)
    | exact resolve eq764501 eq157399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157399 eq764501
  have eq764619 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq764455
       have i₂ := eq213271
       grind)
    | exact superpose eq213271 eq764455
    | exact resolve eq764455 eq213271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213271 eq764455
  have eq764767 : x = y ∨ x ≠ (M.op x y) := by
    first
    | (have i₁ := eq764586
       have i₂ := eq685217
       grind)
    | exact superpose eq685217 eq764586
    | exact resolve eq764586 eq685217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685217 eq764586
  have eq764847 : x = y := by
    first
    | (have r₁ := eq764767
       have r₂ := eq764619
       grind)
    | exact resolve eq764767 eq764619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764619 eq764767
  have eq764902 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq764847
       grind)
    | exact superpose eq764847 eq14
    | exact resolve eq14 eq764847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765323 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq685323
       have i₂ := eq764847
       grind)
    | exact superpose eq764847 eq685323
    | exact resolve eq685323 eq764847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685323
  have eq765562 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq765323
  have eq765815 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq764902
       have i₂ := eq205749
       grind)
    | exact superpose eq205749 eq764902
    | exact resolve eq764902 eq205749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205749 eq764902
  have eq765999 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq765815
       have i₂ := eq765562
       grind)
    | exact superpose eq765562 eq765815
    | exact resolve eq765815 eq765562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765562 eq765815
  have eq766042 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq765999
       have i₂ := eq764847
       grind)
    | exact superpose eq764847 eq765999
    | exact resolve eq765999 eq764847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764847 eq765999
  have eq766043 : False := by grind
  exact eq766043

/-- `Equation4449`: `x ◇ (y ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pxy_Equation4449 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4449 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4449.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k (τ X0) X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | exact resolve eq13 eq15
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X0 X2) X2 X3
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X0 X3
       have i₂ := eq8 x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (τ X1)) X2
       have i₂ := eq16 X1 X0
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X0 X0
       have i₂ := eq12 X2 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq46 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq73 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op X0 X2)
       have i₂ := eq8 X2 X0 X1
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X1 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 (M.op X1 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq26
    | exact resolve eq26 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X1 X3)
       have i₂ := eq26 X3 X1 X0
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X1 X3)
       have i₂ := eq26 X0 X1 X3
       grind)
    | exact superpose eq26 eq8
    | exact resolve eq8 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq26 X2 X1 X0
       grind)
    | (have i₁ := eq8 (M.op X1 X2) X2 X3
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq8
    | exact resolve eq8 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X3 X4) X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X4 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X2 X1
       grind)
    | (have i₁ := eq24 X3 X4 X0 (M.op X0 X2)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq136 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op (M.op (M.op X3 X4) X3) (M.op X1 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X4 X1 (M.op X1 X2)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq24
    | exact resolve eq24 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X5 (M.op X2 X5) X3 X4
       have i₂ := eq24 X0 X1 X5 X2
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op (M.op X0 X0) X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X0 X1 X2
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq24
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X3 X4 (M.op X2 X4)
       have i₂ := eq24 X0 X1 X4 X2
       grind)
    | exact superpose eq24 eq8
    | exact resolve eq8 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq51 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq51 eq13
    | (have j1 := eq51 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq327 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op X5 X3) (M.op (M.op (M.op (M.op X0 X1) X0) X2) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq21 X5 (M.op X2 X5) X3 X4
       have i₂ := eq24 X0 X1 X5 X2
       grind)
    | exact superpose eq24 eq21
    | exact resolve eq21 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq24
  have eq780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq222 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq936 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq780 (σ X0)
       grind)
    | exact superpose eq780 eq13
    | exact resolve eq13 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq936 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq936
    | exact resolve eq936 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1242 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 (σ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq11
    | (have j0 := eq11 X1 (σ X0)
       have j1 := eq47 X0 X0
       grind)
    | (have r₁ := eq11 X0 (σ X1)
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq11 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq1288 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       have j1 := eq11 X1 (σ X0)
       grind)
    | (have r₁ := eq1242 X0 X1
       have r₂ := eq11 X0 (σ X0)
       grind)
    | exact resolve eq1242 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1322 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1288 X0 X1
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq1288
    | (have j0 := eq1288 X0 X1
       grind)
    | exact resolve eq1288 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq2100 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2100 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2100
    | (have j0 := eq2100 X0 X1
       grind)
    | exact resolve eq2100 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq5878 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1322 X0 X1
       have i₂ := eq2210 X2 X0
       grind)
    | exact superpose eq2210 eq1322
    | (have j0 := eq1322 X0 X1
       have j1 := eq2210 X2 X0
       grind)
    | exact resolve eq1322 eq2210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq5900 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5878 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq8061 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq128 X0 (M.op X2 x) X2 X3
       have i₂ := eq135 X0 X1 (M.op (M.op X2 x) X0) X2 x
       grind)
    | exact superpose eq135 eq128
    | exact resolve eq128 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq135
  have eq8413 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8061 x x X0 X1
       have i₂ := eq8061 x x X2 X3
       grind)
    | exact superpose eq8061 eq8061
    | exact resolve eq8061 eq8061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq9146 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 X0 (M.op (M.op x x) x)
       have i₂ := eq136 X1 X0 (M.op (M.op x x) x) x x
       grind)
    | exact superpose eq136 eq26
    | exact resolve eq26 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq10363 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X5) X4) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq8413 X4 X5 X6 (M.op X3 X6)
       have i₂ := eq169 X0 X1 X2 X6 X3
       grind)
    | exact superpose eq169 eq8413
    | exact resolve eq8413 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq10587 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X4 X5) X4) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq73 X4 X5 X2 x
       have i₂ := eq8413 X2 x X0 X1
       grind)
    | (have i₁ := eq73 X4 X5 X2 x
       have i₂ := eq8413 X0 X1 X2 x
       grind)
    | exact superpose eq8413 eq73
    | exact resolve eq73 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10618 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X3 x X2 X3
       have i₂ := eq8413 X3 (M.op x X3) X0 X1
       grind)
    | (have i₁ := eq127 X3 x X2 X3
       have i₂ := eq8413 X0 X1 X3 (M.op x X3)
       grind)
    | exact superpose eq8413 eq127
    | exact resolve eq127 eq8413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13395 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 X0) X1) ∨ (M.op X4 X0) = (k X4 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10618 X1 (M.op X0 X1) X2 X3
       have i₂ := eq44 X0 X1 X4
       grind)
    | exact superpose eq44 eq10618
    | (have j1 := eq44 X0 X1 X4
       grind)
    | exact resolve eq10618 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq13642 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X4 X5) X4) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq73 X4 X5 X2 x
       have i₂ := eq10618 X2 x X0 X1
       grind)
    | exact superpose eq10618 eq73
    | exact resolve eq73 eq10618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq13681 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq127 X1 x X0 X1
       have i₂ := eq10618 X1 (M.op x X1) X2 X3
       grind)
    | exact superpose eq10618 eq127
    | exact resolve eq127 eq10618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq24381 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq222 (M.op X1 X1) X2
       have i₂ := eq147 X1 X0 (M.op X1 X1) X3
       grind)
    | exact superpose eq147 eq222
    | (have j0 := eq222 (M.op X1 X1) X2
       have j1 := eq147 X2 X1 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq222 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq147 X0 (M.op X0 X0) (M.op X0 X0) X3
       grind)
    | exact resolve eq222 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq222
  have eq24619 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (k (M.op X1 X1) X2) ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X1 X2 X3
    first
    | (have j0 := eq24381 x X1 X2 X3
       have j1 := eq13395 X2 X1 X2 X3 (M.op X1 X1)
       grind)
    | (have r₁ := eq24381 (M.op x x) X1 (M.op X3 (M.op X1 X1)) X3
       have r₂ := eq13395 x (M.op (M.op X1 X1) (M.op x x)) (M.op X1 X1) X3 x
       grind)
    | (have r₁ := eq24381 X2 x X1 X3
       have r₂ := eq13395 x X1 X2 (M.op x x) x
       grind)
    | exact resolve eq24381 eq13395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395 eq24381
  have eq33218 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq216 x y X0
       grind)
    | exact superpose eq216 eq14
    | (have j1 := eq216 X0 y X0
       grind)
    | exact resolve eq14 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq33676 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq33218 X0
       have j1 := eq5900 y X0 x
       grind)
    | (have r₁ := eq33218 X0
       have r₂ := eq5900 y x x
       grind)
    | exact resolve eq33218 eq5900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900 eq33218
  have eq33904 : ∀ X0 : G, (k X0 (σ y)) ≠ (k X0 (σ y)) ∨ (k X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq223 X0 X0
       have i₂ := eq33676 X0
       grind)
    | exact superpose eq33676 eq223
    | exact resolve eq223 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33929 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X0 (k X0 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq9146 X0 X1 X0
       have i₂ := eq33676 X0
       grind)
    | exact superpose eq33676 eq9146
    | exact resolve eq9146 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9146
  have eq33990 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq947 X0
       have i₂ := eq33676 (σ X0)
       grind)
    | exact superpose eq33676 eq947
    | exact resolve eq947 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq34029 : ∀ X0 : G, (k X0 X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq33904 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33904
  have eq34052 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq33990 X0
       have i₂ := eq13 X0 y
       grind)
    | exact superpose eq13 eq33990
    | exact resolve eq33990 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33990
  have eq34813 : ∀ X0 X1 : G, (σ (k (k X0 (τ (σ X0))) X1)) = (k (k (σ X0) (σ y)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X0) X1
       have i₂ := eq34029 (σ X0)
       grind)
    | (have i₁ := eq31 X0 (σ y) x
       have i₂ := eq34029 (σ X0)
       grind)
    | exact superpose eq34029 eq31
    | exact resolve eq31 eq34029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq34815 : ∀ X0 : G, (k X0 (τ (σ X0))) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq34029 (σ X0)
       grind)
    | (have i₁ := eq32 X0 (σ y)
       have i₂ := eq34029 (σ X0)
       grind)
    | exact superpose eq34029 eq32
    | exact resolve eq32 eq34029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34875 : ∀ X0 : G, (k X0 (τ (σ X0))) = (k (τ (σ X0)) y) := by
    intro X0
    first
    | (have i₁ := eq34815 X0
       have i₂ := eq20 (σ X0) y
       grind)
    | exact superpose eq20 eq34815
    | exact resolve eq34815 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34815
  have eq34877 : ∀ X0 X1 : G, (σ (k (k X0 (τ (σ X0))) X1)) = (σ (k (k (τ (σ X0)) y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34813 X0 X1
       have i₂ := eq19 (σ X0) y X1
       grind)
    | exact superpose eq19 eq34813
    | exact resolve eq34813 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34813
  have eq34915 : ∀ X0 : G, (k X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq34875 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34875
    | exact resolve eq34875 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34875
  have eq34917 : ∀ X0 X1 : G, (σ (k (k X0 X0) X1)) = (σ (k (k X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34877 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq34877
    | exact resolve eq34877 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34877
  have eq34946 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (σ (k (k X0 y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34917 X0 X1
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq34917
    | exact resolve eq34917 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34917
  have eq35960 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq780 X0
       have i₂ := eq34915 X0
       grind)
    | (have i₁ := eq780 y
       have i₂ := eq34915 y
       grind)
    | exact superpose eq34915 eq780
    | exact resolve eq780 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35967 : ∀ X0 : G, (k X0 (σ y)) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq34029 X0
       have i₂ := eq34915 X0
       grind)
    | (have i₁ := eq34029 y
       have i₂ := eq34915 y
       grind)
    | exact superpose eq34915 eq34029
    | exact resolve eq34029 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34029
  have eq36002 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq34915 (σ X0)
       grind)
    | exact superpose eq34915 eq13
    | exact resolve eq13 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36027 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2210 X0 y
       have i₂ := eq34915 X0
       grind)
    | (have i₁ := eq2210 X0 X0
       have i₂ := eq34915 X0
       grind)
    | exact superpose eq34915 eq2210
    | (have j0 := eq2210 X0 y
       grind)
    | exact resolve eq2210 eq34915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq34915
  have eq36028 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (M.op X0 y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq36027 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq36027
    | exact resolve eq36027 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36027
  have eq36051 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq36002 X0
       have i₂ := eq780 X0
       grind)
    | exact superpose eq780 eq36002
    | exact resolve eq36002 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36002
  have eq37175 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37258 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X1 X2) X1) X3) X4) X0) = (M.op X0 (k X0 y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq143 X1 X2 X3 X0 X0 X4
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq143
    | exact resolve eq143 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq37305 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (k X0 y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8413 X1 X2 X0 X0
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq8413
    | exact resolve eq8413 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37325 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 (k X0 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13681 X1 X2 X0 X0
       have i₂ := eq35960 X0
       grind)
    | exact superpose eq35960 eq13681
    | exact resolve eq13681 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13681
  have eq37340 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X1) X2))) = (k (M.op (M.op X0 X1) X0) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq136 X2 (M.op X0 X1) X0 X0 X1
       have i₂ := eq35960 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq35960 eq136
    | exact resolve eq136 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq37364 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 X2))) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X2 X0 (M.op X0 X1) X1
       have i₂ := eq35960 (M.op X0 X1)
       grind)
    | exact superpose eq35960 eq115
    | exact resolve eq115 eq35960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq35960
  have eq37414 : ∀ X0 X1 : G, (M.op X0 (k X0 (σ y))) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37364 X0 X1 x
       have i₂ := eq33929 X0 x
       grind)
    | exact superpose eq33929 eq37364
    | exact resolve eq37364 eq33929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37364
  have eq37417 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k (M.op X0 X1) (σ y))) = (k (M.op (M.op X0 X1) X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq37340 X0 X1 x
       have i₂ := eq33929 (M.op X0 X1) x
       grind)
    | exact superpose eq33929 eq37340
    | exact resolve eq37340 eq33929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33929 eq37340
  have eq37434 : ∀ X0 X1 : G, (M.op X0 (k X0 y)) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37414 X0 X1
       have i₂ := eq35967 X0
       grind)
    | exact superpose eq35967 eq37414
    | exact resolve eq37414 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37414
  have eq37437 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) y) = (M.op (M.op X0 X1) (k (M.op X0 X1) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37417 X0 X1
       have i₂ := eq35967 (M.op X0 X1)
       grind)
    | exact superpose eq35967 eq37417
    | exact resolve eq37417 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37417
  have eq37449 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) y) = (M.op X0 (k X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq37437 X0 X1
       have i₂ := eq37434 X0 X1
       grind)
    | exact superpose eq37434 eq37437
    | exact resolve eq37437 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37437
  have eq39314 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (k (σ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ y)
       have i₂ := eq35967 (σ X0)
       grind)
    | exact superpose eq35967 eq32
    | exact resolve eq32 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39316 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) y)) = (k (k X0 (σ X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y
       have i₂ := eq35967 (k X0 (σ X1))
       grind)
    | exact superpose eq35967 eq19
    | exact resolve eq19 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq39321 : ∀ X0 : G, (k X0 (τ (σ y))) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq39314 X0
       have i₂ := eq32 X0 y
       grind)
    | exact superpose eq32 eq39314
    | exact resolve eq39314 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39314
  have eq39340 : ∀ X0 : G, (k X0 y) = (k X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq39321 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq39321
    | exact resolve eq39321 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39321
  have eq52893 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) ≠ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X4) ∨ (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq223 (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X1
       have i₂ := eq327 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) X2) X4 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq327 eq223
    | (have r₁ := eq223 (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) (M.op (M.op (M.op X0 X1) X0) X2)
       have r₂ := eq327 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact resolve eq223 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq327
  have eq53084 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq52893 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq52893 X0 X1 X2 x x
       have r₂ := eq10363 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2) x x
       grind)
    | (have r₁ := eq52893 X0 X1 X2 X3 (M.op (M.op (M.op X0 X1) X0) X2)
       have r₂ := eq10363 X0 X1 X2 X3 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact resolve eq52893 eq10363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10363 eq52893
  have eq53212 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) (σ y)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53084 X0 X1 X2 X3 X4
       have i₂ := eq33676 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq33676 eq53084
    | exact resolve eq53084 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53084
  have eq53308 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53212 X0 X1 X2 X3 X4
       have i₂ := eq35967 (M.op (M.op (M.op X0 X1) X0) X2)
       grind)
    | exact superpose eq35967 eq53212
    | exact resolve eq53212 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53212
  have eq53352 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (k (M.op (M.op (M.op X0 X1) X0) X2) y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53308 X0 X1 X2 x X4
       have i₂ := eq37258 (M.op (M.op (M.op X0 X1) X0) X2) X0 X1 X2 x
       grind)
    | exact superpose eq37258 eq53308
    | exact resolve eq53308 eq37258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37258 eq53308
  have eq53386 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X1) X0) (k (M.op (M.op X0 X1) X0) y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53352 X0 X1 X2 X4
       have i₂ := eq37434 (M.op (M.op X0 X1) X0) X2
       grind)
    | exact superpose eq37434 eq53352
    | exact resolve eq53352 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53352
  have eq53415 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) (k (M.op X0 X1) y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53386 X0 X1 X2 X4
       have i₂ := eq37434 (M.op X0 X1) X0
       grind)
    | exact superpose eq37434 eq53386
    | exact resolve eq53386 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53386
  have eq53444 : ∀ X0 X1 X2 X4 : G, (M.op X0 (k X0 y)) = (k (k (M.op (M.op (M.op X0 X1) X0) X2) y) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53415 X0 X1 X2 X4
       have i₂ := eq37434 X0 X1
       grind)
    | exact superpose eq37434 eq53415
    | exact resolve eq53415 eq37434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37434 eq53415
  have eq104375 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = (M.op X3 (k X3 y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37325 X3 X2 (k X2 y)
       have i₂ := eq37305 X2 X0 X1
       grind)
    | exact superpose eq37305 eq37325
    | exact resolve eq37325 eq37305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37305 eq37325
  have eq159849 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ y)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 y
       have i₂ := eq37175 (σ X0) X1
       grind)
    | exact superpose eq37175 eq32
    | (have j1 := eq37175 (σ X0) X1
       grind)
    | exact resolve eq32 eq37175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37175
  have eq159962 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 y) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq159849 X0 X1
       have i₂ := eq39340 X0
       grind)
    | exact superpose eq39340 eq159849
    | (have j0 := eq159849 X0 X1
       grind)
    | exact resolve eq159849 eq39340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159849
  have eq159995 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq159962 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq159962
    | (have j0 := eq159962 X0 X1
       grind)
    | exact resolve eq159962 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159962
  have eq212590 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) X0)) = (σ (k (M.op (M.op X2 X3) X2) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34052 (M.op (M.op X2 X3) X2)
       have i₂ := eq10587 X0 X1 (M.op (M.op X2 X3) X2) X2 X3
       grind)
    | exact superpose eq10587 eq34052
    | exact resolve eq34052 eq10587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10587 eq34052
  have eq212784 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X0)) = (σ (M.op X2 (k X2 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212590 X0 X1 X2 x
       have i₂ := eq37449 X2 x
       grind)
    | exact superpose eq37449 eq212590
    | exact resolve eq212590 eq37449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37449 eq212590
  have eq267879 : ∀ X0 X1 : G, (k (k X0 y) X1) = (τ (σ (k (M.op X0 X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (k X0 y) X1)
       have i₂ := eq34946 X0 X1
       grind)
    | exact superpose eq34946 eq9
    | exact resolve eq9 eq34946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34946
  have eq267882 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (k (k X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq267879 X0 X1
       have i₂ := eq9 (k (M.op X0 X0) X1)
       grind)
    | exact superpose eq9 eq267879
    | exact resolve eq267879 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267879
  have eq383077 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (M.op (M.op X2 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq212784 X2 X3 (M.op (M.op x x) x)
       have i₂ := eq13642 X0 X1 (k (M.op (M.op x x) x) y) x x
       grind)
    | exact superpose eq13642 eq212784
    | exact resolve eq212784 eq13642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13642 eq212784
  have eq466117 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq24619 X0 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24619
  have eq466118 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq466117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466117
  have eq466138 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (k X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq267882 X0 X0
       have i₂ := eq466118 X0
       grind)
    | exact superpose eq466118 eq267882
    | exact resolve eq267882 eq466118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267882
  have eq466324 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (k (k X0 y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8413 X1 X2 X0 X0
       have i₂ := eq466138 X0
       grind)
    | exact superpose eq466138 eq8413
    | exact resolve eq8413 eq466138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq466343 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (k (k X0 y) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10618 X0 X0 X1 X2
       have i₂ := eq466138 X0
       grind)
    | exact superpose eq466138 eq10618
    | exact resolve eq10618 eq466138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10618 eq466138
  have eq467838 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k (k (τ y) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq39340 (k (τ y) y)
       have i₂ := eq466324 (τ y) X0 X1
       grind)
    | exact superpose eq466324 eq39340
    | exact resolve eq39340 eq466324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39340 eq466324
  have eq469313 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (k (σ (k (τ X2) y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (k (τ X2) y)
       have i₂ := eq466343 (τ X2) X0 X1
       grind)
    | exact superpose eq466343 eq16
    | exact resolve eq16 eq466343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq466343
  have eq469353 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (k (k X2 (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469313 X0 X1 X2
       have i₂ := eq15 X2 y
       grind)
    | exact superpose eq15 eq469313
    | exact resolve eq469313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq469313
  have eq469745 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (k (k X2 y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469353 X0 X1 X2
       have i₂ := eq35967 X2
       grind)
    | exact superpose eq35967 eq469353
    | exact resolve eq469353 eq35967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469353
  have eq480276 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (σ (k (k (τ y) y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq383077 X0 X1 x x
       have i₂ := eq467838 x x
       grind)
    | exact superpose eq467838 eq383077
    | exact resolve eq383077 eq467838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383077 eq467838
  have eq480441 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (k (k y (σ y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480276 X0 X1
       have i₂ := eq39316 y y
       grind)
    | exact superpose eq39316 eq480276
    | exact resolve eq480276 eq39316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39316 eq480276
  have eq480508 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (k (M.op y y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480441 X0 X1
       have i₂ := eq33676 y
       grind)
    | exact superpose eq33676 eq480441
    | exact resolve eq480441 eq33676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33676 eq480441
  have eq480535 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op (M.op y y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480508 X0 X1
       have i₂ := eq466118 y
       grind)
    | exact superpose eq466118 eq480508
    | exact resolve eq480508 eq466118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466118 eq480508
  have eq485800 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X1 X0))) = (M.op X2 (k X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53444 X2 x x (M.op (M.op (M.op X2 x) X2) x)
       have i₂ := eq469745 X0 X1 (M.op (M.op (M.op X2 x) X2) x)
       grind)
    | exact superpose eq469745 eq53444
    | exact resolve eq53444 eq469745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53444 eq469745
  have eq672449 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 y) ∨ y = (k y y) := by
    intro X0
    first
    | (have i₁ := eq35967 X0
       have i₂ := eq159995 y X0
       grind)
    | exact superpose eq159995 eq35967
    | (have j1 := eq159995 y x
       grind)
    | exact resolve eq35967 eq159995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35967 eq159995
  have eq672454 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq672449 X0
       have i₂ := eq780 y
       grind)
    | exact superpose eq780 eq672449
    | (have j0 := eq672449 X0
       grind)
    | exact resolve eq672449 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq672449
  have eq672467 : (σ (M.op x y)) ≠ (k (σ x) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq672454 (σ x)
       grind)
    | exact superpose eq672454 eq14
    | exact resolve eq14 eq672454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672454
  have eq672468 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq672467
       have i₂ := eq36051 x
       grind)
    | exact superpose eq36051 eq672467
    | exact resolve eq672467 eq36051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36051 eq672467
  have eq672469 : y = (M.op y y) := by
    first
    | (have r₁ := eq672468
       have r₂ := eq36028 x
       grind)
    | exact resolve eq672468 eq36028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36028 eq672468
  have eq672898 : ∀ X0 X1 : G, (M.op X1 (k X1 y)) = (M.op X0 (M.op y y)) := by
    intro X0 X1
    first
    | (have i₁ := eq104375 y y X0 X1
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq104375
    | exact resolve eq104375 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104375
  have eq672974 : (M.op y y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq480535 y y
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq480535
    | exact resolve eq480535 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480535
  have eq672988 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq485800 y y X0
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq485800
    | exact resolve eq485800 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485800
  have eq673005 : ∀ X0 : G, (σ y) = (M.op X0 (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq672988 X0
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq672988
    | exact resolve eq672988 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672988
  have eq673019 : y = (σ y) := by
    first
    | (have i₁ := eq672974
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq672974
    | exact resolve eq672974 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672974
  have eq673090 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 (k X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq672898 X0 X1
       have i₂ := eq672469
       grind)
    | exact superpose eq672469 eq672898
    | exact resolve eq672898 eq672469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672469 eq672898
  have eq673392 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq673090 X0 x
       have i₂ := eq673005 x
       grind)
    | exact superpose eq673005 eq673090
    | exact resolve eq673090 eq673005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673005 eq673090
  have eq673573 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq673392 X0
       have i₂ := eq673019
       grind)
    | exact superpose eq673019 eq673392
    | exact resolve eq673392 eq673019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673392
  have eq673778 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq673019
       grind)
    | exact superpose eq673019 eq14
    | exact resolve eq14 eq673019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673947 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq673778
       have i₂ := eq673573 (σ x)
       grind)
    | exact superpose eq673573 eq673778
    | exact resolve eq673778 eq673573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673778
  have eq673969 : y ≠ (σ y) := by
    first
    | (have i₁ := eq673947
       have i₂ := eq673573 x
       grind)
    | exact superpose eq673573 eq673947
    | exact resolve eq673947 eq673573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673573 eq673947
  have eq673980 : False := by grind
  exact eq673980

/-- `Equation4449`: `x ◇ (y ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4449 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4449 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4449.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
    intro X0 X1 X2
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X0 X3)
       have i₂ := eq8 X3 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 X0 (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 X0 X0
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq28 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X1 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X2 (M.op X1 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X3 (M.op X1 X3)
       have i₂ := eq22 X3 X1 X0
       grind)
    | (have i₁ := eq8 X2 X3 (M.op X1 X3)
       have i₂ := eq22 X0 X1 X3
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq33 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq33 eq13
    | (have j1 := eq33 (σ X0) X2 X2
       grind)
    | exact resolve eq13 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq146 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X1 X0))) = (M.op (M.op (M.op X3 X4) X3) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X3 X4 (M.op X1 X2) X2
       have i₂ := eq22 X2 X1 X0
       grind)
    | (have i₁ := eq20 X3 X4 (M.op X1 X2) X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq20
    | exact resolve eq20 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq153 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X4 X5) X4) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq20 X4 X5 x X2
       have i₂ := eq20 X0 X1 x X2
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1240 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1460 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | (have j0 := eq32 X1 X1
       grind)
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1460 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq1460
    | (have j0 := eq1460 X0 X1
       grind)
    | exact resolve eq1460 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq2151 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 X0
       have i₂ := eq1531 X2 X0
       grind)
    | exact superpose eq1531 eq11
    | (have j0 := eq11 X1 X0
       have j1 := eq1531 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq1531 X0 X1
       grind)
    | exact resolve eq11 eq1531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq2189 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2151 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2151
  have eq3775 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (σ (k X2 X1)) = (σ (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2189 X1 (τ X0) X2
       grind)
    | exact superpose eq2189 eq15
    | (have j1 := eq2189 X1 X1 X2
       grind)
    | exact resolve eq15 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq2189
  have eq3815 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = X0 ∨ (σ (k X2 X1)) = (σ (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3775 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3775
    | (have j0 := eq3775 X0 X1 X2
       grind)
    | exact resolve eq3775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq5644 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1240 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1240
    | (have j0 := eq1240 (τ X0)
       grind)
    | exact resolve eq1240 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1240
  have eq5660 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5644 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5644
    | (have j0 := eq5644 X0
       grind)
    | exact resolve eq5644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq5667 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5660 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5660
    | (have j0 := eq5660 X0
       grind)
    | exact resolve eq5660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5660
  have eq6026 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq128 x y X0
       grind)
    | exact superpose eq128 eq14
    | (have j1 := eq128 x x X0
       grind)
    | exact resolve eq14 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq6122 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq6026 X0
       have j1 := eq3815 X0 x x
       grind)
    | (have r₁ := eq6026 X0
       have r₂ := eq3815 X0 x y
       grind)
    | exact resolve eq6026 eq3815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815 eq6026
  have eq6153 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5667 (σ x)
       have i₂ := eq6122 (σ x)
       grind)
    | exact superpose eq6122 eq5667
    | (have j0 := eq5667 (σ x)
       grind)
    | (have r₁ := eq5667 (σ x)
       have r₂ := eq6122 (σ x)
       grind)
    | exact resolve eq5667 eq6122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6172 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (σ x)
       have i₂ := eq6122 (σ X0)
       grind)
    | exact superpose eq6122 eq40
    | exact resolve eq40 eq6122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq6122
  have eq6177 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6153
  have eq6179 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq6172 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq6172
    | exact resolve eq6172 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6172
  have eq6190 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq6179 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq6179
    | exact resolve eq6179 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6179
  have eq6334 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5667 x
       have i₂ := eq6190 x
       grind)
    | exact superpose eq6190 eq5667
    | (have j0 := eq5667 x
       grind)
    | (have r₁ := eq5667 x
       have r₂ := eq6190 x
       grind)
    | exact resolve eq5667 eq6190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667 eq6190
  have eq6355 : x = (M.op x x) := by grind
  clear eq6334
  have eq6772 : ∀ X0 X1 : G, (M.op x (M.op x x)) = (M.op X0 (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 x x X0 X1
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq90
    | exact resolve eq90 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq6775 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 x x X0 X1
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq102
    | exact resolve eq102 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq6782 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op x x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 X0 X1 X2 x x
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq153
    | exact resolve eq153 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6797 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6782 X0 X1 X2
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq6782
    | exact resolve eq6782 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6782
  have eq6802 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6775 X0 X1
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq6775
    | exact resolve eq6775 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq6804 : ∀ X0 X1 : G, (M.op x x) = (M.op X0 (M.op (M.op x X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6772 X0 X1
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq6772
    | exact resolve eq6772 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6772
  have eq6819 : ∀ X1 : G, (M.op x x) = (M.op x (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq6804 x X1
       have i₂ := eq6802 x (M.op x X1)
       grind)
    | exact superpose eq6802 eq6804
    | exact resolve eq6804 eq6802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6804
  have eq6830 : ∀ X1 : G, x = (M.op x (M.op x X1)) := by
    intro X1
    first
    | (have i₁ := eq6819 X1
       have i₂ := eq6355
       grind)
    | exact superpose eq6355 eq6819
    | exact resolve eq6819 eq6355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6355 eq6819
  have eq6976 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 (M.op (M.op X3 X4) X2))) = (M.op (M.op (M.op X5 X6) X5) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq146 X2 (M.op X3 X4) X3 X5 X6
       have i₂ := eq153 X3 X4 (M.op X2 (M.op (M.op X3 X4) X2)) X0 X1
       grind)
    | (have i₁ := eq146 X2 (M.op X3 X4) X3 X5 X6
       have i₂ := eq153 X0 X1 (M.op X2 (M.op (M.op X3 X4) X2)) X3 X4
       grind)
    | exact superpose eq153 eq146
    | exact resolve eq146 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq7504 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 (M.op (M.op X3 X4) X2))) = (M.op x X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6976 X0 X1 X2 X3 X4 x x
       have i₂ := eq6797 x x X3
       grind)
    | exact superpose eq6797 eq6976
    | exact resolve eq6976 eq6797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6976
  have eq7751 : ∀ X2 X3 X4 : G, (M.op x X3) = (M.op x (M.op X2 (M.op (M.op X3 X4) X2))) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq7504 x x X2 X3 X4
       have i₂ := eq6797 x x (M.op X2 (M.op (M.op X3 X4) X2))
       grind)
    | exact superpose eq6797 eq7504
    | exact resolve eq7504 eq6797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7504
  have eq7978 : ∀ X3 X4 : G, (M.op x X3) = (M.op x (M.op x (M.op X3 X4))) := by
    intro X3 X4
    first
    | (have i₁ := eq7751 x X3 X4
       have i₂ := eq6802 x (M.op X3 X4)
       grind)
    | exact superpose eq6802 eq7751
    | exact resolve eq7751 eq6802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6802 eq7751
  have eq8123 : ∀ X3 : G, x = (M.op x X3) := by
    intro X3
    first
    | (have i₁ := eq7978 X3 x
       have i₂ := eq6830 (M.op X3 x)
       grind)
    | exact superpose eq6830 eq7978
    | exact resolve eq7978 eq6830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6830 eq7978
  have eq38012 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (σ x) (σ x)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq153 X0 X1 X2 (σ x) (σ x)
       have i₂ := eq6177
       grind)
    | exact superpose eq6177 eq153
    | exact resolve eq153 eq6177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq38068 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38012 X0 X1 X2
       have i₂ := eq6177
       grind)
    | exact superpose eq6177 eq38012
    | exact resolve eq38012 eq6177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38012
  have eq38133 : ∀ X2 : G, (M.op x X2) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq38068 x x X2
       have i₂ := eq6797 x x X2
       grind)
    | exact superpose eq6797 eq38068
    | exact resolve eq38068 eq6797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6797 eq38068
  have eq38192 : ∀ X2 : G, x = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq38133 X2
       have i₂ := eq8123 X2
       grind)
    | exact superpose eq8123 eq38133
    | exact resolve eq38133 eq8123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38133
  have eq39238 : x ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq38192 (σ y)
       grind)
    | exact superpose eq38192 eq14
    | exact resolve eq14 eq38192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39239 : x = (σ x) := by
    first
    | (have i₁ := eq6177
       have i₂ := eq38192 (σ x)
       grind)
    | exact superpose eq38192 eq6177
    | exact resolve eq6177 eq38192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6177 eq38192
  have eq39486 : x ≠ (σ x) := by
    first
    | (have i₁ := eq39238
       have i₂ := eq8123 y
       grind)
    | exact superpose eq8123 eq39238
    | exact resolve eq39238 eq8123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8123 eq39238
  have eq39536 : False := by grind
  exact eq39536

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
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
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq86 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq82 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq82 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq82 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq86 (σ X0) (σ X1)
       grind)
    | exact superpose eq86 eq13
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq102
    | exact resolve eq102 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq102
  have eq932 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq14
    | (have r₁ := eq14
       have r₂ := eq107 x y
       grind)
    | exact resolve eq14 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq956 : False := by grind
  exact eq956

/-- `Equation4460`: `x ◇ (y ◇ x) = (z ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4460 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4460 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
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
  have eq20 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 X1 x X3
       have i₂ := eq8 X1 x X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq20 X2 (M.op X1 (M.op X2 X2)) X0
       grind)
    | (have i₁ := eq8 (M.op X2 X2) X1 X3
       have i₂ := eq20 X0 (M.op X1 (M.op X2 X2)) X2
       grind)
    | exact superpose eq20 eq8
    | exact resolve eq8 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26
    | exact resolve eq26 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq12 X0 (σ X1)
       grind)
    | exact superpose eq12 eq26
    | (have j1 := eq12 X0 (σ X1)
       grind)
    | exact resolve eq26 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq31
    | exact resolve eq31 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq157 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq143 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq143
    | exact resolve eq143 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq368 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq157 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq157
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq157 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq645 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq157
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq157 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq717 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq1860 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1936 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq10
    | (have j1 := eq36 X0 X1
       grind)
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1964 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1860 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq1860
    | (have j0 := eq1860 X0 X1
       grind)
    | exact resolve eq1860 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq2030 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq3887 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq128 X0 X0
       grind)
    | exact superpose eq128 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq128 X0 X0
       grind)
    | exact resolve eq12 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq6512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq660
       have i₂ := eq2030 y x
       grind)
    | exact superpose eq2030 eq660
    | (have j1 := eq2030 y x
       grind)
    | (have r₁ := eq660
       have r₂ := eq2030 y x
       grind)
    | exact resolve eq660 eq2030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq6513 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq660
       have i₂ := eq1964 y x
       grind)
    | exact superpose eq1964 eq660
    | (have j1 := eq1964 (σ y) (σ x)
       grind)
    | (have r₁ := eq660
       have r₂ := eq1964 y x
       grind)
    | exact resolve eq660 eq1964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq6514 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6513
  have eq6515 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by grind
  clear eq6512
  have eq6525 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq157 x
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq157
    | exact resolve eq157 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6584 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6525
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq6525
    | exact resolve eq6525 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6525
  have eq6679 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6682 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1964 y x
       have i₂ := eq6584
       grind)
    | exact superpose eq6584 eq1964
    | (have j0 := eq1964 y x
       grind)
    | exact resolve eq1964 eq6584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964 eq6584
  have eq6683 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq6682
  have eq6684 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq6679
  have eq8276 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq682 x x
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq682
    | exact resolve eq682 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq8340 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8276
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8276
    | exact resolve eq8276 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8276
  have eq8356 : x = (k x (τ (σ y))) ∨ x = (k x y) := by
    first
    | (have i₁ := eq157 x
       have i₂ := eq6515
       grind)
    | exact superpose eq6515 eq157
    | exact resolve eq157 eq6515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq6515
  have eq8425 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq8356
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq8356
    | exact resolve eq8356 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8356
  have eq8426 : x = (k x y) := by grind
  clear eq8425
  have eq15907 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq368 (σ X1) X0
       grind)
    | exact superpose eq368 eq26
    | (have j1 := eq368 (σ X1) X0
       grind)
    | exact resolve eq26 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq368
  have eq15937 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15907 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq15907
    | (have j0 := eq15907 X0 X1
       grind)
    | exact resolve eq15907 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq15973 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15937 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq15937
    | (have j0 := eq15937 X0 X1
       grind)
    | exact resolve eq15937 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15937
  have eq27926 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq8340
       grind)
    | exact superpose eq8340 eq9
    | exact resolve eq9 eq8340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq27982 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27926
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27926
    | exact resolve eq27926 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27926
  have eq28763 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq31 x x
       have i₂ := eq27982
       grind)
    | exact superpose eq27982 eq31
    | exact resolve eq31 eq27982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27982
  have eq28771 : y = (M.op x x) ∨ x = y := by grind
  clear eq28763
  have eq29935 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq28771
       grind)
    | exact superpose eq28771 eq8
    | exact resolve eq8 eq28771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31299 : (M.op x y) = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq29935 x x
       have i₂ := eq28771
       grind)
    | exact superpose eq28771 eq29935
    | exact resolve eq29935 eq28771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28771
  have eq31534 : (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq31299
  have eq32734 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq29935 x y
       have i₂ := eq31534
       grind)
    | exact superpose eq31534 eq29935
    | exact resolve eq29935 eq31534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29935 eq31534
  have eq32735 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq32734
  have eq39240 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq135 x (M.op x y)
       have i₂ := eq32735
       grind)
    | exact superpose eq32735 eq135
    | (have j0 := eq135 x y
       grind)
    | exact resolve eq135 eq32735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32735
  have eq83750 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15973 x x
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq15973
    | (have j0 := eq15973 x x
       grind)
    | exact resolve eq15973 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15973
  have eq83835 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83750
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq83750
    | exact resolve eq83750 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83750
  have eq96260 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83835
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq83835
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq83835 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83835
  have eq96327 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq96260
  have eq98142 : x ≠ y ∨ x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq135 x x
       have i₂ := eq96327
       grind)
    | exact superpose eq96327 eq135
    | (have j0 := eq135 x x
       grind)
    | (have r₁ := eq135 x x
       have r₂ := eq96327
       grind)
    | exact resolve eq135 eq96327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98189 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq96327
  have eq98190 : x ≠ y ∨ x = (k x x) := by
    first
    | (have j1 := eq135 x x
       grind)
    | (have r₁ := eq98142
       have r₂ := eq135 x x
       grind)
    | exact resolve eq98142 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq98142
  have eq168612 : x ≠ x ∨ x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39240
       have i₂ := eq6684
       grind)
    | exact superpose eq6684 eq39240
    | (have r₁ := eq39240
       have r₂ := eq6684
       grind)
    | exact resolve eq39240 eq6684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6684 eq39240
  have eq168613 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq168612
  have eq168614 : x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq168613
       have r₂ := eq98190
       grind)
    | exact resolve eq168613 eq98190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98190 eq168613
  have eq169516 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq713 x
       have i₂ := eq168614
       grind)
    | exact superpose eq168614 eq713
    | (have j0 := eq713 x
       grind)
    | exact resolve eq713 eq168614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168614
  have eq169543 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq169516
  have eq173734 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6514
       have i₂ := eq169543
       grind)
    | exact superpose eq169543 eq6514
    | exact resolve eq6514 eq169543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173745 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 (σ x)
       have i₂ := eq169543
       grind)
    | exact superpose eq169543 eq8
    | exact resolve eq8 eq169543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169543
  have eq173868 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq173734
  have eq243951 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq173745 (σ x) (σ x)
       have i₂ := eq6514
       grind)
    | exact superpose eq6514 eq173745
    | exact resolve eq173745 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514 eq173745
  have eq244137 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq243951
  have eq246169 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq244137
       grind)
    | exact superpose eq244137 eq14
    | exact resolve eq14 eq244137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244137
  have eq249412 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq246169
       have i₂ := eq6683
       grind)
    | exact superpose eq6683 eq246169
    | exact resolve eq246169 eq6683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6683 eq246169
  have eq249413 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq249412
  have eq249415 : y = (M.op x x) := by
    first
    | (have r₁ := eq249413
       have r₂ := eq173868
       grind)
    | exact resolve eq249413 eq173868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173868 eq249413
  have eq252362 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq8
    | exact resolve eq8 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252366 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1 x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq20
    | exact resolve eq20 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq252376 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq69 x X0
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq69
    | exact resolve eq69 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq252378 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) y) = (M.op (M.op X0 X0) (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 X1 x x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq71
    | exact resolve eq71 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq254775 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq252362 (σ X1) (σ X0)
       have i₂ := eq717 X1 X0
       grind)
    | exact superpose eq717 eq252362
    | (have j1 := eq717 X1 X0
       grind)
    | exact resolve eq252362 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq254801 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq252362 x x
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq252362
    | exact resolve eq252362 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258401 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq258492 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq258401 X0 X1
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq258401
    | (have j0 := eq258401 X0 X1
       grind)
    | exact resolve eq258401 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258401
  have eq261262 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k (σ X0) X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 (τ X1))
       have i₂ := eq1936 X0 X1
       grind)
    | exact superpose eq1936 eq9
    | (have j1 := eq1936 X0 X1
       grind)
    | exact resolve eq9 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261267 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1936 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq261268 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq261267 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq261267
    | (have j0 := eq261267 X0
       grind)
    | exact resolve eq261267 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261267
  have eq261273 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op X0 (τ X1)) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261262 X0 X1
       have i₂ := eq41 X0 X1
       grind)
    | exact superpose eq41 eq261262
    | (have j0 := eq261262 X0 X1
       grind)
    | exact resolve eq261262 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq261262
  have eq279852 : (M.op y y) = (k (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq252376 y
       have i₂ := eq252362 y y
       grind)
    | exact superpose eq252362 eq252376
    | exact resolve eq252376 eq252362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252362 eq252376
  have eq279966 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by
    first
    | (have i₁ := eq261268 (M.op y y)
       have i₂ := eq279852
       grind)
    | exact superpose eq279852 eq261268
    | (have j0 := eq261268 (M.op y y)
       grind)
    | (have r₁ := eq261268 (M.op y y)
       have r₂ := eq279852
       grind)
    | exact resolve eq261268 eq279852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261268 eq279852
  have eq279971 : (M.op y y) = (σ (M.op (τ (M.op y y)) (τ (M.op y y)))) := by grind
  clear eq279966
  have eq296355 : ∀ X0 X1 : G, (M.op (M.op X1 X1) y) = X0 ∨ (τ (k (M.op y y) X0)) = (τ (M.op (M.op y y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252378 y y X1
       have i₂ := eq258492 X0 (M.op y y)
       grind)
    | (have i₁ := eq252378 X0 X1 x
       have i₂ := eq258492 (M.op (M.op X0 X0) (M.op X1 y)) X1
       grind)
    | exact superpose eq258492 eq252378
    | (have j1 := eq258492 X0 (M.op y y)
       grind)
    | exact resolve eq252378 eq258492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252378 eq258492
  have eq296389 : ∀ X0 : G, (M.op y y) = X0 ∨ (τ (k (M.op y y) X0)) = (τ (M.op (M.op y y) X0)) := by
    intro X0
    first
    | (have i₁ := eq296355 X0 x
       have i₂ := eq252366 x y
       grind)
    | exact superpose eq252366 eq296355
    | (have j0 := eq296355 X0 x
       grind)
    | exact resolve eq296355 eq252366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296355
  have eq296468 : ∀ X0 : G, (τ (M.op y X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq296389 X0
       have i₂ := eq252366 y X0
       grind)
    | exact superpose eq252366 eq296389
    | (have j0 := eq296389 X0
       grind)
    | exact resolve eq296389 eq252366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296389
  have eq317270 : (τ (M.op y y)) = (M.op (τ (M.op y y)) (τ (M.op y y))) := by
    first
    | (have i₁ := eq9 (M.op (τ (M.op y y)) (τ (M.op y y)))
       have i₂ := eq279971
       grind)
    | exact superpose eq279971 eq9
    | exact resolve eq9 eq279971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319331 : ∀ X0 : G, (M.op y X0) = (M.op (τ (M.op y y)) X0) := by
    intro X0
    first
    | (have i₁ := eq252366 (τ (M.op y y)) X0
       have i₂ := eq317270
       grind)
    | exact superpose eq317270 eq252366
    | exact resolve eq252366 eq317270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252366
  have eq324706 : ∀ X0 : G, (M.op y y) = X0 ∨ (M.op (τ (M.op y y)) (τ X0)) = (k (τ (M.op y y)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq279971
       have i₂ := eq261273 (τ (M.op y y)) X0
       grind)
    | (have i₁ := eq279971
       have i₂ := eq261273 X0 (σ (M.op (τ (M.op y y)) (τ (M.op y y))))
       grind)
    | exact superpose eq261273 eq279971
    | (have j1 := eq261273 (τ (M.op y y)) X0
       grind)
    | exact resolve eq279971 eq261273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261273 eq279971
  have eq324717 : ∀ X0 : G, (τ (k (M.op y y) X0)) = (M.op (τ (M.op y y)) (τ X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq324706 X0
       have i₂ := eq72 X0 (M.op y y)
       grind)
    | exact superpose eq72 eq324706
    | (have j0 := eq324706 X0
       grind)
    | exact resolve eq324706 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq324706
  have eq324730 : ∀ X0 : G, (M.op y (τ X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq324717 X0
       have i₂ := eq319331 (τ X0)
       grind)
    | exact superpose eq319331 eq324717
    | (have j0 := eq324717 X0
       grind)
    | exact resolve eq324717 eq319331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319331 eq324717
  have eq434994 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq3887 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq434995 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq434994 X0 X1
       have j1 := eq645 X1 X0
       grind)
    | (have r₁ := eq434994 (k X1 X1) X0
       have r₂ := eq645 X0 X1
       grind)
    | (have r₁ := eq434994 X0 (σ (k X1 X1))
       have r₂ := eq645 (σ X0) X1
       grind)
    | (have r₁ := eq434994 X1 X0
       have r₂ := eq645 X0 X1
       grind)
    | exact resolve eq434994 eq645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645 eq434994
  have eq435017 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq434995 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq434995 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq434995 eq16
    | (have j1 := eq434995 (τ X1) X0
       grind)
    | exact resolve eq16 eq434995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq435018 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq434995 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq434995 X0 (σ X0)
       grind)
    | exact superpose eq434995 eq9
    | (have j1 := eq434995 X1 X0
       grind)
    | exact resolve eq9 eq434995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434995
  have eq435029 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq435017 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq435017
    | (have j0 := eq435017 X0 X1
       grind)
    | exact resolve eq435017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435017
  have eq435035 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq435029 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq435029
    | (have j0 := eq435029 X0 X1
       grind)
    | exact resolve eq435029 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435029
  have eq435183 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq435035 (τ X1) X0
       grind)
    | exact superpose eq435035 eq17
    | (have j1 := eq435035 (τ X1) X0
       grind)
    | exact resolve eq17 eq435035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq435035
  have eq435475 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq435018 (σ X1) X0
       grind)
    | exact superpose eq435018 eq13
    | (have j1 := eq435018 (σ X1) X0
       grind)
    | exact resolve eq13 eq435018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435018
  have eq435480 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq435475 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq435475
    | (have j0 := eq435475 X0 X1
       grind)
    | exact resolve eq435475 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435475
  have eq436287 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq435480 x y
       grind)
    | exact superpose eq435480 eq14
    | (have j1 := eq435480 x y
       grind)
    | exact resolve eq14 eq435480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435480
  have eq436378 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq436287
       have i₂ := eq8426
       grind)
    | exact superpose eq8426 eq436287
    | exact resolve eq436287 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436287
  have eq455620 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq435183 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq435183
    | exact resolve eq435183 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435183
  have eq455647 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq455620 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq455620
    | (have j0 := eq455620 X0 X1
       grind)
    | exact resolve eq455620 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455620
  have eq455671 : (σ (M.op x y)) = (σ x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq455647 y x
       have i₂ := eq8426
       grind)
    | exact superpose eq8426 eq455647
    | (have j0 := eq455647 y x
       grind)
    | exact resolve eq455647 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8426 eq455647
  have eq455779 : y = (k x x) := by
    first
    | (have r₁ := eq455671
       have r₂ := eq436378
       grind)
    | exact resolve eq455671 eq436378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436378 eq455671
  have eq455859 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq713 x
       have i₂ := eq455779
       grind)
    | exact superpose eq455779 eq713
    | (have j0 := eq713 x
       grind)
    | exact resolve eq713 eq455779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq532025 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq296468 X0
       have i₂ := eq324730 X0
       grind)
    | exact superpose eq324730 eq296468
    | (have j0 := eq296468 X0
       have j1 := eq324730 X0
       grind)
    | exact resolve eq296468 eq324730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296468 eq324730
  have eq532028 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op y X0)) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have j0 := eq532025 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532025
  have eq532065 : ∀ X0 : G, (M.op y X0) = (σ (M.op y (τ X0))) ∨ (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y X0)
       have i₂ := eq532028 X0
       grind)
    | exact superpose eq532028 eq10
    | (have j1 := eq532028 X0
       grind)
    | exact resolve eq10 eq532028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532028
  have eq532108 : ∀ X0 : G, (σ (M.op y X0)) = (M.op y (σ X0)) ∨ (σ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq532065 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq532065
    | (have j0 := eq532065 (σ X0)
       grind)
    | exact resolve eq532065 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532065
  have eq532646 : (σ (M.op x y)) = (M.op y (σ x)) ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq532108 x
       have i₂ := eq254801
       grind)
    | exact superpose eq254801 eq532108
    | (have j0 := eq532108 x
       grind)
    | exact resolve eq532108 eq254801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254801 eq532108
  have eq608343 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq254775 x x
       have i₂ := eq455779
       grind)
    | exact superpose eq455779 eq254775
    | exact resolve eq254775 eq455779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254775 eq455779
  have eq608378 : (σ (M.op x y)) ≠ (M.op y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq14
       have i₂ := eq608343
       grind)
    | exact superpose eq608343 eq14
    | exact resolve eq14 eq608343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608343
  have eq609195 : (M.op y (σ x)) ≠ (M.op y (σ x)) ∨ x = y ∨ (σ x) = (M.op y y) := by
    first
    | (have i₁ := eq608378
       have i₂ := eq532646
       grind)
    | exact superpose eq532646 eq608378
    | (have r₁ := eq608378
       have r₂ := eq532646
       grind)
    | exact resolve eq608378 eq532646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532646 eq608378
  have eq609197 : (σ x) = (M.op y y) ∨ x = y := by grind
  clear eq609195
  have eq609943 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq317270
       have i₂ := eq609197
       grind)
    | exact superpose eq609197 eq317270
    | exact resolve eq317270 eq609197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317270 eq609197
  have eq610669 : x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq609943
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq609943
    | exact resolve eq609943 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609943
  have eq610741 : x = (M.op x x) := by
    first
    | (have r₁ := eq610669
       have r₂ := eq98189
       grind)
    | exact resolve eq610669 eq98189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98189 eq610669
  have eq610804 : x = y := by
    first
    | (have i₁ := eq249415
       have i₂ := eq610741
       grind)
    | exact superpose eq610741 eq249415
    | exact resolve eq249415 eq610741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610741
  have eq613169 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq610804
       grind)
    | exact superpose eq610804 eq14
    | exact resolve eq14 eq610804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613636 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq455859
       have i₂ := eq610804
       grind)
    | exact superpose eq610804 eq455859
    | exact resolve eq455859 eq610804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455859
  have eq613736 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq613636
  have eq613886 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq613169
       have i₂ := eq249415
       grind)
    | exact superpose eq249415 eq613169
    | exact resolve eq613169 eq249415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249415 eq613169
  have eq614005 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq613886
       have i₂ := eq613736
       grind)
    | exact superpose eq613736 eq613886
    | exact resolve eq613886 eq613736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613736 eq613886
  have eq614043 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq614005
       have i₂ := eq610804
       grind)
    | exact superpose eq610804 eq614005
    | exact resolve eq614005 eq610804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610804 eq614005
  have eq614044 : False := by grind
  exact eq614044

/-- `Equation4461`: `x ◇ (y ◇ x) = (z ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_pyy_pxy_Equation4461 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4461 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq21 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 (M.op X2 X2) X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq8 x X1 X3
       have i₂ := eq8 x X1 X0
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq8 X2 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X3
       have i₂ := eq12 X3 X0
       grind)
    | (have i₁ := eq8 X0 X1 X2
       have i₂ := eq12 X0 (M.op X2 X2)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
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
  have eq46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq60 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq107 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq141 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 X3 (M.op X1 X3)
       have i₂ := eq8 X3 X1 X0
       grind)
    | exact superpose eq8 eq27
    | exact resolve eq27 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 X2 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq27 X0 X1 X2
       have i₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12 eq27
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq27 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27 X2 (M.op X3 X3) X1
       have i₂ := eq8 X0 X1 X3
       grind)
    | exact superpose eq8 eq27
    | exact resolve eq27 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (M.op (M.op X0 X0) (k X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq27
  have eq170 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq24 X2 X1 X0
       grind)
    | (have i₁ := eq60 X2 X1
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq60
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (k X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X2 X1
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq60
    | exact resolve eq60 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (k X1 (M.op X1 X1)) = (M.op (k X0 (M.op X0 X0)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 x
       have i₂ := eq63 X0 x (M.op X1 X1)
       grind)
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63
  have eq374 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq640 : ∀ X0 X2 X3 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X3 X3) (M.op X2 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq8 x (M.op X2 X2) X3
       have i₂ := eq170 X2 x X0
       grind)
    | exact superpose eq170 eq8
    | exact resolve eq8 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq689 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X4 (M.op X5 (M.op X4 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq23 X5 X4 x x
       have i₂ := eq23 X1 X0 x x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1717 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X0 (M.op X0 X0)) = (k (M.op X2 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 (M.op x x) (M.op X2 X2)
       have i₂ := eq640 X0 X2 x
       grind)
    | exact superpose eq640 eq374
    | exact resolve eq374 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1719 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq374 (M.op X0 X0) (M.op X1 X1)
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq374
    | exact resolve eq374 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1724 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq374 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq1728 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1
    grind
  clear eq1719
  have eq1730 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 X0)) = (k (M.op X2 X2) (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1717 X0 X1 X2
       grind)
    | (have r₁ := eq1717 X0 X2 X2
       have r₂ := eq640 X0 X2 X2
       grind)
    | exact resolve eq1717 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1958 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1724 (σ X0)
       grind)
    | exact superpose eq1724 eq13
    | exact resolve eq13 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1960 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0 X0
       have i₂ := eq1724 (τ X0)
       grind)
    | exact superpose eq1724 eq46
    | exact resolve eq46 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq1967 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1960 X0
       have i₂ := eq1724 X0
       grind)
    | exact superpose eq1724 eq1960
    | exact resolve eq1960 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq1969 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1958 X0
       have i₂ := eq1724 X0
       grind)
    | exact superpose eq1724 eq1958
    | exact resolve eq1958 eq1724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724 eq1958
  have eq2051 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (τ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (τ X0)
       have i₂ := eq1967 X0
       grind)
    | exact superpose eq1967 eq8
    | exact resolve eq8 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 X1 X2 : G, (k X1 (M.op X1 X1)) = (M.op (M.op X2 X2) (τ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq640 X1 (τ X0) X2
       have i₂ := eq1967 X0
       grind)
    | exact superpose eq1967 eq640
    | exact resolve eq640 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq1967
  have eq2244 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) (σ X0) X1
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq8
    | exact resolve eq8 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2256 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2 (σ X0)
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq8
    | exact resolve eq8 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2264 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 X2 (σ X0)
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq24
    | exact resolve eq24 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2377 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  clear eq43
  have eq2455 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2377 X0 X1
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq2377
    | (have j0 := eq2377 X0 X1
       grind)
    | exact resolve eq2377 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2527 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2455 X0 X1
       have i₂ := eq9 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq2455
    | (have j0 := eq2455 X0 X1
       grind)
    | exact resolve eq2455 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq3679 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ (σ (M.op X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2256 (σ X0) X1 X2
       have i₂ := eq1969 X0
       grind)
    | exact superpose eq1969 eq2256
    | exact resolve eq2256 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969
  have eq18990 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))) = (M.op (k X2 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq232 X0 (M.op X2 X2)
       have i₂ := eq8 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq8 eq232
    | exact resolve eq232 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq30294 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2527 x y
       grind)
    | exact superpose eq2527 eq14
    | (have j1 := eq2527 x y
       grind)
    | exact resolve eq14 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq30797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30294
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq30294
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq30294 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30294
  have eq30803 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq30797
  have eq30804 : y = (M.op x x) := by grind
  clear eq30803
  have eq31492 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq8
    | exact resolve eq8 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31493 : (k x y) = (M.op y y) := by grind
  have eq31524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 x X2 X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq141
    | exact resolve eq141 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq31550 : ∀ X0 : G, (k x y) = (k (M.op X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq1728 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1728
    | exact resolve eq1728 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq31552 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k y (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 X1 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1730
    | exact resolve eq1730 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31553 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (k (M.op X1 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1730 X0 x X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq1730
    | exact resolve eq1730 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31561 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X1 X1) (τ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2077 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2077
    | exact resolve eq2077 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq31570 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2244 x X0
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2244
    | exact resolve eq2244 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq31571 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2256 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2256
    | exact resolve eq2256 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq31572 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2264 x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq2264
    | exact resolve eq2264 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq31597 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 x x X0 X1
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq145
    | exact resolve eq145 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq31600 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq171 x x X0
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq171
    | exact resolve eq171 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31604 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 X1 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq689
    | exact resolve eq689 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq31621 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq31570 x
       have i₂ := eq31572 x (σ x)
       grind)
    | exact superpose eq31572 eq31570
    | exact resolve eq31570 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31570
  have eq31630 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (σ y) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq31561 X0 x
       have i₂ := eq31572 x (τ y)
       grind)
    | exact superpose eq31572 eq31561
    | exact resolve eq31561 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31561
  have eq31638 : ∀ X1 : G, (k (M.op X1 X1) y) = (M.op x (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31553 x X1
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31553
    | exact resolve eq31553 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31553
  have eq31639 : ∀ X1 : G, (k y (M.op X1 X1)) = (M.op x (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq31552 x X1
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31552
    | exact resolve eq31552 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31552
  have eq31661 : ∀ X1 X2 : G, (M.op (M.op X2 X1) (M.op y X2)) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq31524 x X1 X2
       have i₂ := eq31571 x X1
       grind)
    | exact superpose eq31571 eq31524
    | exact resolve eq31524 eq31571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31524
  have eq31700 : (M.op x (M.op x y)) = (M.op (σ y) (τ y)) := by
    first
    | (have i₁ := eq31630 x
       have i₂ := eq31600 x
       grind)
    | exact superpose eq31600 eq31630
    | exact resolve eq31630 eq31600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31600 eq31630
  have eq31703 : (k x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31638 x
       have i₂ := eq31550 x
       grind)
    | exact superpose eq31550 eq31638
    | exact resolve eq31638 eq31550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31550 eq31638
  have eq31743 : (M.op y y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31703
       have i₂ := eq31493
       grind)
    | exact superpose eq31493 eq31703
    | exact resolve eq31703 eq31493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31493 eq31703
  have eq39575 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X2)) = (M.op (M.op X3 X3) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq146 X3 X2
       have i₂ := eq1730 X3 X1 X0
       grind)
    | (have i₁ := eq146 (M.op X2 X2) X1
       have i₂ := eq1730 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq1730 eq146
    | exact resolve eq146 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq39862 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (M.op X1 X1) (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171 (k X1 (M.op X1 X1)) (M.op X1 X1) X2
       have i₂ := eq146 X1 X0
       grind)
    | exact superpose eq146 eq171
    | exact resolve eq171 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq171
  have eq39887 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39862 X0 X1 X2
       have i₂ := eq31572 X1 (M.op (k X1 (M.op X1 X1)) (M.op X0 (M.op (M.op X1 X1) X0)))
       grind)
    | exact superpose eq31572 eq39862
    | exact resolve eq39862 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39862
  have eq40016 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X2)) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39575 X0 X1 X2 X3
       have i₂ := eq31572 X3 (k (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq31572 eq39575
    | exact resolve eq39575 eq31572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31572 eq39575
  have eq40219 : ∀ X0 X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39887 X0 X1 X2
       have i₂ := eq18990 X0 X1 X1
       grind)
    | exact superpose eq18990 eq39887
    | exact resolve eq39887 eq18990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18990 eq39887
  have eq40304 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40016 X0 X1 x x
       have i₂ := eq31597 x x
       grind)
    | exact superpose eq31597 eq40016
    | exact resolve eq40016 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40016
  have eq40480 : ∀ X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op x (M.op x y)))) := by
    intro X1 X2
    first
    | (have i₁ := eq40219 x X1 X2
       have i₂ := eq31597 x X1
       grind)
    | exact superpose eq31597 eq40219
    | exact resolve eq40219 eq31597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31597 eq40219
  have eq40563 : ∀ X0 X1 : G, (M.op y y) = (M.op (σ y) (k (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40304 X0 X1
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq40304
    | exact resolve eq40304 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40304
  have eq40711 : ∀ X1 X2 : G, (k X2 (M.op X2 X2)) = (M.op (σ y) (k (M.op X1 X1) (M.op y y))) := by
    intro X1 X2
    first
    | (have i₁ := eq40480 X1 X2
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq40480
    | exact resolve eq40480 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40480
  have eq40903 : ∀ X2 : G, (k X2 (M.op X2 X2)) = (M.op y y) := by
    intro X2
    first
    | (have i₁ := eq40711 x X2
       have i₂ := eq40563 x y
       grind)
    | exact superpose eq40563 eq40711
    | exact resolve eq40711 eq40563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40563 eq40711
  have eq44369 : ∀ X0 X1 : G, (k X1 X0) = (M.op y y) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40903 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq40903 x
       have i₂ := eq12 X0 (M.op x x)
       grind)
    | exact superpose eq12 eq40903
    | (have j1 := eq12 y (k X1 X0)
       grind)
    | exact resolve eq40903 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40903
  have eq47176 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (M.op y X2) ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31492 X1 X2
       have i₂ := eq41 X2 X0 X1 X3
       grind)
    | exact superpose eq41 eq31492
    | (have j1 := eq41 X2 X1 X2 X3
       grind)
    | exact resolve eq31492 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47265 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq31492 x x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq31492
    | exact resolve eq31492 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47391 : ∀ X0 X2 : G, (M.op (τ (M.op X2 X2)) X0) = (M.op y X0) := by
    intro X0 X2
    first
    | (have i₁ := eq2051 X2 x X0
       have i₂ := eq31492 x X0
       grind)
    | exact superpose eq31492 eq2051
    | exact resolve eq2051 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051
  have eq47396 : ∀ X0 X2 : G, (M.op (σ (σ (M.op X2 X2))) X0) = (M.op y X0) := by
    intro X0 X2
    first
    | (have i₁ := eq3679 X2 x X0
       have i₂ := eq31492 x X0
       grind)
    | exact superpose eq31492 eq3679
    | exact resolve eq3679 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47459 : ∀ X0 X1 X2 : G, (M.op (σ (σ (M.op X2 X2))) X1) = (M.op (M.op X0 X1) (M.op y X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3679 X2 (M.op X0 X1) X1
       have i₂ := eq31492 X1 X0
       grind)
    | exact superpose eq31492 eq3679
    | exact resolve eq3679 eq31492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679 eq31492
  have eq47628 : ∀ X1 X2 : G, (M.op (σ (σ (M.op X2 X2))) X1) = (M.op (σ y) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq47459 x X1 X2
       have i₂ := eq31661 X1 x
       grind)
    | exact superpose eq31661 eq47459
    | exact resolve eq47459 eq31661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31661 eq47459
  have eq47875 : ∀ X2 X3 : G, (M.op y X2) = (M.op x (M.op x y)) ∨ (M.op X3 X2) = (k X3 X2) := by
    intro X2 X3
    first
    | (have i₁ := eq47176 x x X2 X3
       have i₂ := eq31604 x x
       grind)
    | exact superpose eq31604 eq47176
    | (have j0 := eq47176 x x X2 X3
       grind)
    | exact resolve eq47176 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31604 eq47176
  have eq47967 : ∀ X1 : G, (M.op y X1) = (M.op (σ y) X1) := by
    intro X1
    first
    | (have i₁ := eq47628 X1 x
       have i₂ := eq47396 X1 x
       grind)
    | exact superpose eq47396 eq47628
    | exact resolve eq47628 eq47396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47396 eq47628
  have eq48141 : ∀ X2 X3 : G, (M.op X3 X2) = (k X3 X2) ∨ (M.op y y) = (M.op y X2) := by
    intro X2 X3
    first
    | (have i₁ := eq47875 X2 X3
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq47875
    | (have j0 := eq47875 X2 X3
       grind)
    | exact resolve eq47875 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47875
  have eq137862 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq47391 X0 x
       have i₂ := eq30804
       grind)
    | exact superpose eq30804 eq47391
    | exact resolve eq47391 eq30804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30804 eq47391
  have eq139744 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op (τ y) X1)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1 (τ y)
       have i₂ := eq137862 X0
       grind)
    | exact superpose eq137862 eq142
    | exact resolve eq142 eq137862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq139963 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (τ y)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq139744 X0 x
       have i₂ := eq31571 x (τ y)
       grind)
    | exact superpose eq31571 eq139744
    | (have j0 := eq139744 X0 x
       grind)
    | exact resolve eq139744 eq31571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31571 eq139744
  have eq140259 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op x y)) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq139963 X0
       have i₂ := eq31700
       grind)
    | exact superpose eq31700 eq139963
    | (have j0 := eq139963 X0
       grind)
    | exact resolve eq139963 eq31700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31700 eq139963
  have eq140463 : ∀ X0 : G, (M.op y y) = (M.op y X0) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq140259 X0
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq140259
    | (have j0 := eq140259 X0
       grind)
    | exact resolve eq140259 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140259
  have eq166743 : ∀ X0 X1 : G, (k y X0) = (M.op x (M.op x y)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq31639 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq31639 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq31639
    | (have j1 := eq12 X1 X0
       grind)
    | exact resolve eq31639 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31639
  have eq166960 : ∀ X0 X1 : G, (M.op y y) = (k y X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq166743 X0 X1
       have i₂ := eq31743
       grind)
    | exact superpose eq31743 eq166743
    | (have j0 := eq166743 X0 X1
       grind)
    | exact resolve eq166743 eq31743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31743 eq166743
  have eq207742 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq47967 (σ x)
       have i₂ := eq31621
       grind)
    | exact superpose eq31621 eq47967
    | exact resolve eq47967 eq31621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31621 eq47967
  have eq210776 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq207742
       grind)
    | exact superpose eq207742 eq14
    | exact resolve eq14 eq207742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207742
  have eq1159253 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op y y) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44369 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44369
  have eq1229210 : ∀ X0 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1159253 (τ y) X0
       have i₂ := eq137862 X0
       grind)
    | exact superpose eq137862 eq1159253
    | (have j0 := eq1159253 y X0
       grind)
    | (have r₁ := eq1159253 (τ y) y
       have r₂ := eq137862 y
       grind)
    | exact resolve eq1159253 eq137862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137862 eq1159253
  have eq1229217 : ∀ X0 : G, (M.op y X0) = (k (τ y) X0) := by
    intro X0
    first
    | (have j0 := eq1229210 X0
       have j1 := eq140463 X0
       grind)
    | (have r₁ := eq1229210 X0
       have r₂ := eq140463 X0
       grind)
    | (have r₁ := eq1229210 y
       have r₂ := eq140463 y
       grind)
    | exact resolve eq1229210 eq140463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140463 eq1229210
  have eq1229258 : ∀ X0 : G, (σ (M.op y X0)) = (k y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0
       have i₂ := eq1229217 X0
       grind)
    | exact superpose eq1229217 eq16
    | exact resolve eq16 eq1229217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1229217
  have eq1374660 : ∀ X0 : G, (M.op y y) ≠ (M.op y X0) ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq166960 X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166960
  have eq1374662 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq1374660 X0
       have j1 := eq48141 X0 y
       grind)
    | (have r₁ := eq1374660 x
       have r₂ := eq48141 x x
       grind)
    | (have r₁ := eq1374660 y
       have r₂ := eq48141 y x
       grind)
    | exact resolve eq1374660 eq48141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48141 eq1374660
  have eq1374723 : ∀ X0 : G, (M.op y (σ X0)) = (σ (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1229258 X0
       have i₂ := eq1374662 (σ X0)
       grind)
    | exact superpose eq1374662 eq1229258
    | exact resolve eq1229258 eq1374662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229258 eq1374662
  have eq1382749 : (σ (M.op x y)) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq1374723 x
       have i₂ := eq47265
       grind)
    | exact superpose eq47265 eq1374723
    | exact resolve eq1374723 eq47265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47265 eq1374723
  have eq1382928 : False := by grind
  exact eq1382928

/-- `Equation4470`: `x ◇ (y ◇ y) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_y_x_pxy_Equation4470 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4470 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4470.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X0) X1) := by
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
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X1) X2) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 X2
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq8 X0 X1
       have i₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X2 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq33 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq30
    | exact resolve eq30 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (k (τ X1) X0) = (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1
       have i₂ := eq12 (τ X1) X0
       grind)
    | (have i₁ := eq25 X0
       have i₂ := eq12 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq12 eq25
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq135 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (M.op X0 X0) X2
       have i₂ := eq29 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq29 eq8
    | (have j1 := eq29 X1 X1 (M.op X0 X0)
       grind)
    | exact resolve eq8 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X1)) = (M.op (M.op X2 X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq29 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq29 eq13
    | (have j1 := eq29 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq41
  have eq167 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq151 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq151
    | exact resolve eq151 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq185 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k (M.op X0 X0) X2) ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 X0) X2
       have i₂ := eq29 X1 X0 X2
       grind)
    | exact superpose eq29 eq49
    | (have j0 := eq49 (M.op X0 X0) X2
       have j1 := eq29 X1 X1 X2
       grind)
    | (have r₁ := eq49 (M.op X0 X0) X2
       have r₂ := eq29 X0 X0 X2
       grind)
    | exact resolve eq49 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq186 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 (M.op X0 X0) X1
       have i₂ := eq8 X0 X1
       grind)
    | exact superpose eq8 eq49
    | (have j0 := eq49 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq49 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq8 (M.op X1 X1) X1
       grind)
    | exact resolve eq49 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq12 (σ X1) X0
       grind)
    | (have i₁ := eq167 X0
       have i₂ := eq12 X0 (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq12 eq167
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq167 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq12 (σ X0) X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 X0 (M.op (σ X0) (σ X1))
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 (σ X1) X0
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq33 x y
       grind)
    | exact superpose eq33 eq14
    | (have j1 := eq33 x y
       grind)
    | exact resolve eq14 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq308 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq9
    | (have j1 := eq33 X0 X1
       grind)
    | exact resolve eq9 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 X1 : G, (k X1 (τ (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq167 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq167
    | (have j1 := eq33 X1 X0
       grind)
    | exact resolve eq167 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq333 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq318
    | (have j0 := eq318 X0 X1
       grind)
    | exact resolve eq318 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq338 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq13 X0 (k X0 X0)
       grind)
    | exact superpose eq13 eq300
    | (have j0 := eq300 X0
       grind)
    | exact resolve eq300 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq740 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq822 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq740 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq740
    | (have j0 := eq740 X0 X1
       grind)
    | exact resolve eq740 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq1581 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 (σ X0)
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq8
    | (have j1 := eq44 X0 X0
       grind)
    | exact resolve eq8 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1583 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq44 X0 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 (σ X0) X1
       have j1 := eq44 X0 X0
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq295
       have i₂ := eq822 y x
       grind)
    | exact superpose eq822 eq295
    | (have j1 := eq822 (σ y) (σ x)
       grind)
    | (have r₁ := eq295
       have r₂ := eq822 y x
       grind)
    | exact resolve eq295 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1837 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq1836
  have eq1848 : x = (k x (τ (σ y))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq167
    | exact resolve eq167 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq1851 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq8
    | exact resolve eq8 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1864 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq49 (σ x) (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq49
    | (have j0 := eq49 (σ x) (σ x)
       grind)
    | exact resolve eq49 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1867 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1864
       have i₂ := eq13 x x
       grind)
    | exact superpose eq13 eq1864
    | exact resolve eq1864 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1871 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1848
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1848
    | exact resolve eq1848 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1955 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq822 y x
       have i₂ := eq1871
       grind)
    | exact superpose eq1871 eq822
    | (have j0 := eq822 y x
       grind)
    | exact resolve eq822 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq1871
  have eq1956 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq1955
  have eq1987 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq308 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308
    | exact resolve eq308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2007 : (σ y) = (σ (k x x)) ∨ x = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq308 x x
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq308
    | exact resolve eq308 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq2036 : (σ y) = (σ (k x x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2007
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2007
    | exact resolve eq2007 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2039 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1987 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1987
    | (have j0 := eq1987 X0 X1
       grind)
    | exact resolve eq1987 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq2526 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq281
    | (have j0 := eq281 X1 (τ X0)
       grind)
    | exact resolve eq281 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2637 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2526 X0 X1
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq2526
    | (have j0 := eq2526 X0 X1
       grind)
    | exact resolve eq2526 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2526
  have eq2647 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2637 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2637
    | (have j0 := eq2637 X0 X1
       grind)
    | exact resolve eq2637 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq5608 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (M.op (σ X0) (σ X0)) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq5609 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5608 X0 X1
       have i₂ := eq8 (σ X0) (σ X0)
       grind)
    | exact superpose eq8 eq5608
    | (have j0 := eq5608 X0 X1
       grind)
    | exact resolve eq5608 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608
  have eq5628 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (σ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq91
    | (have j0 := eq91 X1 (σ X0)
       grind)
    | exact resolve eq91 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq5699 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5628 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq5628
    | (have j0 := eq5628 X0 X1
       grind)
    | exact resolve eq5628 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq8917 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq2039 X0 X1
       grind)
    | exact superpose eq2039 eq24
    | (have j1 := eq2039 X0 X1
       grind)
    | exact resolve eq24 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039
  have eq9717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq295
       have i₂ := eq2647 x y
       grind)
    | exact superpose eq2647 eq295
    | (have j1 := eq2647 x y
       grind)
    | (have r₁ := eq295
       have r₂ := eq2647 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq295
       have r₂ := eq2647 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq295 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq2647
  have eq9787 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = y := by grind
  clear eq9717
  have eq10671 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq244 (σ X1) X0
       grind)
    | exact superpose eq244 eq24
    | (have j1 := eq244 (σ X1) X0
       grind)
    | exact resolve eq24 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq244
  have eq10701 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 (τ (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10671 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq10671
    | (have j0 := eq10671 X0 X1
       grind)
    | exact resolve eq10671 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10671
  have eq10740 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10701 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq10701
    | (have j0 := eq10701 X0 X1
       grind)
    | exact resolve eq10701 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10701
  have eq17480 : (k x x) = (τ (σ y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9 (k x x)
       have i₂ := eq2036
       grind)
    | exact superpose eq2036 eq9
    | exact resolve eq9 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq17552 : y = (k x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17480
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq17480
    | exact resolve eq17480 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq18205 : y = (M.op x x) ∨ x = y ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq30 x x
       have i₂ := eq17552
       grind)
    | exact superpose eq17552 eq30
    | exact resolve eq30 eq17552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17552
  have eq18233 : y = (M.op x x) ∨ x = y := by grind
  clear eq18205
  have eq27786 : (k x x) = (τ (σ y)) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10740 x x
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq10740
    | (have j0 := eq10740 x x
       grind)
    | exact resolve eq10740 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27881 : y = (k x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27786
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq27786
    | exact resolve eq27786 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27786
  have eq33534 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5699 x x
       have i₂ := eq27881
       grind)
    | exact superpose eq27881 eq5699
    | exact resolve eq5699 eq27881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5699 eq27881
  have eq33538 : x = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq33534
  have eq42519 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq338 x
       have i₂ := eq33538
       grind)
    | exact superpose eq33538 eq338
    | (have j0 := eq338 x
       grind)
    | exact resolve eq338 eq33538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq33538
  have eq42560 : (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq42519
       have r₂ := eq1867
       grind)
    | exact resolve eq42519 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867 eq42519
  have eq42564 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq330 x
       grind)
    | (have r₁ := eq42560
       have r₂ := eq330 x
       grind)
    | exact resolve eq42560 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq42560
  have eq43404 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1837
       have i₂ := eq42564
       grind)
    | exact superpose eq42564 eq1837
    | exact resolve eq1837 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43431 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq8 X0 (σ x)
       have i₂ := eq42564
       grind)
    | exact superpose eq42564 eq8
    | exact resolve eq8 eq42564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42564
  have eq43543 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq43404
  have eq81414 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8917 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8917
    | (have j0 := eq8917 X1 (τ X0)
       grind)
    | exact resolve eq8917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81499 : ∀ X0 : G, (k (τ (σ X0)) X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq8917 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81500 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq81499 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq81499
    | (have j0 := eq81499 X0
       grind)
    | exact resolve eq81499 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81499
  have eq81539 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81414 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq81414
    | (have j0 := eq81414 X0 X1
       grind)
    | exact resolve eq81414 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81414
  have eq81624 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq81500 X0
       have i₂ := eq30 X0 X0
       grind)
    | exact superpose eq30 eq81500
    | (have j0 := eq81500 X0
       have j1 := eq30 X0 X0
       grind)
    | (have r₁ := eq81500 X0
       have r₂ := eq30 X0 X0
       grind)
    | exact resolve eq81500 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81660 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq81624 X0
       have j1 := eq81500 X0
       grind)
    | (have r₁ := eq81624 X0
       have r₂ := eq81500 X0
       grind)
    | exact resolve eq81624 eq81500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81624
  have eq81716 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (τ (M.op (σ X1) (σ X1))) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq81660 X1
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq81660 X0
       have i₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12 eq81660
    | (have j0 := eq81660 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq81660 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq81660 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq81660 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81660
  have eq82654 : (τ (σ y)) = (k (τ (σ x)) x) ∨ x = (τ (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq8917 (σ x) x
       have i₂ := eq9787
       grind)
    | exact superpose eq9787 eq8917
    | exact resolve eq8917 eq9787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8917 eq9787
  have eq82698 : (k x x) = (τ (σ y)) ∨ x = (τ (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq82654
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq82654
    | exact resolve eq82654 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82654
  have eq82719 : y = (k x x) ∨ x = (τ (σ y)) ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq82698
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82698
    | exact resolve eq82698 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82698
  have eq82720 : y = (k x x) ∨ x = (τ (σ y)) ∨ x = y := by grind
  clear eq82719
  have eq82728 : x = y ∨ y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq82720
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq82720
    | exact resolve eq82720 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82720
  have eq82729 : y = (k x x) ∨ x = y := by grind
  clear eq82728
  have eq84681 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (σ (τ X0))) = (M.op X1 (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1581 (τ X0) X1
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1581
    | exact resolve eq1581 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq84689 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X1 (k X0 X0)) ∨ (σ (τ X0)) = (k X0 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84681 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84681
    | (have j0 := eq84681 X0 X1
       grind)
    | exact resolve eq84681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84681
  have eq84693 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op X1 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84689 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84689
    | (have j0 := eq84689 X0 X1
       grind)
    | exact resolve eq84689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84689
  have eq87942 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (k X1 X1)) ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1
       have i₂ := eq84693 X1 X0
       grind)
    | exact superpose eq84693 eq8
    | (have j1 := eq84693 X1 X1
       grind)
    | exact resolve eq8 eq84693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84693
  have eq88948 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1851 (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq1851
    | exact resolve eq1851 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq89013 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq88948
  have eq91005 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq87942 X0 x
       have i₂ := eq82729
       grind)
    | exact superpose eq82729 eq87942
    | exact resolve eq87942 eq82729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82729 eq87942
  have eq91046 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq91005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91005
  have eq91131 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x x)) = (M.op X0 (M.op (M.op x x) y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8 X0 (M.op x x)
       have i₂ := eq91046 (M.op x x)
       grind)
    | exact superpose eq91046 eq8
    | exact resolve eq8 eq91046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91046
  have eq91308 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x x)) = (M.op X0 (M.op x (M.op y y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq91131 X0
       have i₂ := eq8 x y
       grind)
    | exact superpose eq8 eq91131
    | exact resolve eq91131 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91131
  have eq92340 : ∀ X0 X1 : G, (σ X0) ≠ X1 ∨ (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq92341 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq92340 X0 X1
       have j1 := eq281 X1 X0
       grind)
    | (have r₁ := eq92340 (k X1 X1) X0
       have r₂ := eq281 X0 X1
       grind)
    | (have r₁ := eq92340 X0 (σ (k X1 X1))
       have r₂ := eq281 (σ X0) X1
       grind)
    | (have r₁ := eq92340 X1 X0
       have r₂ := eq281 X0 X1
       grind)
    | exact resolve eq92340 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq92340
  have eq92408 : ∀ X0 X1 : G, (k X1 (σ (τ X1))) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X1)
       have i₂ := eq92341 (τ X1) X0
       grind)
    | (have i₁ := eq16 X0 X1
       have i₂ := eq92341 X0 (σ (k (τ X0) X1))
       grind)
    | exact superpose eq92341 eq16
    | (have j1 := eq92341 (τ X1) X0
       grind)
    | exact resolve eq16 eq92341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92409 : ∀ X0 X1 : G, (τ X0) = (k X1 X1) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq92341 X1 X0
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq92341 X0 (σ X0)
       grind)
    | exact superpose eq92341 eq9
    | (have j1 := eq92341 X1 X0
       grind)
    | exact resolve eq9 eq92341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92341
  have eq92467 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq92408 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq92408
    | (have j0 := eq92408 X0 X1
       grind)
    | exact resolve eq92408 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92408
  have eq92477 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92467 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92467
    | (have j0 := eq92467 X0 X1
       grind)
    | exact resolve eq92467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92467
  have eq92621 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq92477
  have eq94687 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq92409 (σ X1) X0
       grind)
    | exact superpose eq92409 eq13
    | (have j1 := eq92409 (σ X1) X0
       grind)
    | exact resolve eq13 eq92409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92409
  have eq94711 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94687 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq94687
    | (have j0 := eq94687 X0 X1
       grind)
    | exact resolve eq94687 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94687
  have eq96691 : ∀ X0 : G, y ≠ y ∨ y = (k y X0) ∨ (k X0 x) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq185 x x x
       have i₂ := eq18233
       grind)
    | exact superpose eq18233 eq185
    | (have j0 := eq185 X0 x X0
       grind)
    | exact resolve eq185 eq18233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq18233
  have eq96693 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ y = (k y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq96691 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96691
  have eq98488 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op X0 (M.op X0 X0)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5609 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5609
    | exact resolve eq5609 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq98489 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (M.op X0 X0)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98488 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq98488
    | (have j0 := eq98488 X0 X1
       grind)
    | exact resolve eq98488 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98488
  have eq98492 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op X0 (M.op X0 X0)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98489 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq98489
    | (have j0 := eq98489 X0 X1
       grind)
    | exact resolve eq98489 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq98489
  have eq100525 : y ≠ y ∨ y = (τ (M.op (σ y) (σ y))) ∨ (M.op y x) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq81500 y
       have i₂ := eq96693 y
       grind)
    | exact superpose eq96693 eq81500
    | (have j0 := eq81500 y
       have j1 := eq96693 y
       grind)
    | (have r₁ := eq81500 y
       have r₂ := eq96693 y
       grind)
    | exact resolve eq81500 eq96693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81500 eq96693
  have eq100556 : y = (τ (M.op (σ y) (σ y))) ∨ (M.op y x) = (k y x) ∨ x = y := by grind
  clear eq100525
  have eq100585 : y = (τ (M.op (σ y) (σ y))) ∨ (M.op y x) = (k y x) := by
    first
    | (have j1 := eq81716 x y
       grind)
    | (have r₁ := eq100556
       have r₂ := eq81716 y (τ (M.op (σ y) (σ y)))
       grind)
    | (have r₁ := eq100556
       have r₂ := eq81716 (τ (M.op (σ y) (σ y))) y
       grind)
    | (have r₁ := eq100556
       have r₂ := eq81716 (M.op y x) (k y x)
       grind)
    | exact resolve eq100556 eq81716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81716 eq100556
  have eq101078 : y = (k y y) ∨ y = (k y y) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq10740 y y
       have i₂ := eq100585
       grind)
    | exact superpose eq100585 eq10740
    | (have j0 := eq10740 y y
       grind)
    | exact resolve eq10740 eq100585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10740 eq100585
  have eq101103 : y = (k y y) ∨ (M.op y x) = (k y x) := by grind
  clear eq101078
  have eq101201 : (τ y) = (τ (M.op y y)) ∨ (τ y) = (τ (M.op y y)) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq81539 y y
       have i₂ := eq101103
       grind)
    | exact superpose eq101103 eq81539
    | (have j0 := eq81539 y y
       grind)
    | exact resolve eq81539 eq101103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81539 eq101103
  have eq101202 : (τ y) = (τ (M.op y y)) ∨ (M.op y x) = (k y x) := by grind
  clear eq101201
  have eq101255 : ∀ X0 : G, (k (τ y) (τ X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq52 X0 (M.op y y)
       have i₂ := eq101202
       grind)
    | exact superpose eq101202 eq52
    | exact resolve eq52 eq101202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101202
  have eq101266 : ∀ X0 : G, (τ (k y X0)) = (τ (k (M.op y y) X0)) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq101255 X0
       have i₂ := eq52 X0 y
       grind)
    | exact superpose eq52 eq101255
    | exact resolve eq101255 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq101255
  have eq110978 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq43431 (σ x)
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq43431
    | exact resolve eq43431 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq43431
  have eq111034 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq110978
  have eq111049 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq89013
       have i₂ := eq111034
       grind)
    | exact superpose eq111034 eq89013
    | exact resolve eq89013 eq111034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89013 eq111034
  have eq111077 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq111049
  have eq111286 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq111077
       grind)
    | exact superpose eq111077 eq14
    | exact resolve eq14 eq111077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111077
  have eq111344 : (σ x) ≠ (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq111286
       have i₂ := eq1956
       grind)
    | exact superpose eq1956 eq111286
    | exact resolve eq111286 eq1956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956 eq111286
  have eq111347 : (σ x) ≠ (σ y) ∨ y = (M.op x x) := by grind
  clear eq111344
  have eq111349 : y = (M.op x x) := by
    first
    | (have r₁ := eq111347
       have r₂ := eq43543
       grind)
    | exact resolve eq111347 eq43543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43543 eq111347
  have eq111369 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq8 x X0
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq8
    | exact resolve eq8 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111424 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k (M.op X0 X0) x) := by
    intro X0
    first
    | (have i₁ := eq186 X0 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq186
    | (have j0 := eq186 X0 x
       grind)
    | exact resolve eq186 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq111612 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op X0 X0)) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq135 x x x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq135
    | exact resolve eq135 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq111820 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq111369 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq111369
    | exact resolve eq111369 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111369
  have eq126485 : (M.op y y) = (k (M.op y y) x) := by
    first
    | (have j0 := eq111424 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111424
  have eq127824 : (M.op y y) = (M.op y x) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq111612 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq111612
    | exact resolve eq111612 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111612
  have eq127889 : (M.op x y) = (M.op y y) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq127824
       have i₂ := eq111820
       grind)
    | exact superpose eq111820 eq127824
    | exact resolve eq127824 eq111820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127824
  have eq127905 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq127889
       have i₂ := eq111820
       grind)
    | exact superpose eq111820 eq127889
    | exact resolve eq127889 eq111820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127889
  have eq187230 : ∀ X0 : G, (k (M.op y y) X0) = (σ (τ (k y X0))) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op y y) X0)
       have i₂ := eq101266 X0
       grind)
    | exact superpose eq101266 eq10
    | exact resolve eq10 eq101266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101266
  have eq187234 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ (M.op y x) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq187230 X0
       have i₂ := eq10 (k y X0)
       grind)
    | exact superpose eq10 eq187230
    | exact resolve eq187230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187230
  have eq187238 : ∀ X0 : G, (k y X0) = (k (M.op y y) X0) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq187234 X0
       have i₂ := eq111820
       grind)
    | exact superpose eq111820 eq187234
    | (have j0 := eq187234 X0
       grind)
    | exact resolve eq187234 eq111820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111820 eq187234
  have eq187262 : (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq126485
       have i₂ := eq187238 x
       grind)
    | exact superpose eq187238 eq126485
    | exact resolve eq126485 eq187238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126485 eq187238
  have eq187408 : (M.op x y) ≠ (M.op y y) ∨ (M.op x y) = (k y x) := by grind
  clear eq187262
  have eq187411 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq187408
       have r₂ := eq127905
       grind)
    | exact resolve eq187408 eq127905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127905 eq187408
  have eq200033 : ∀ X0 X1 : G, (k X1 X0) ≠ (M.op X1 (M.op X1 X1)) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq98492 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98492
    | exact resolve eq98492 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98492
  have eq200057 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq200033 X1 X0
       have i₂ := eq92621 X0
       grind)
    | exact superpose eq92621 eq200033
    | (have j0 := eq200033 X1 X0
       have j1 := eq92621 X0
       grind)
    | exact resolve eq200033 eq92621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92621 eq200033
  have eq200084 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq200057 X0 X1
       have j1 := eq30 X1 X0
       grind)
    | (have r₁ := eq200057 X1 X0
       have r₂ := eq30 X0 X1
       grind)
    | exact resolve eq200057 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq200057
  have eq200175 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq200084 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200084
  have eq200176 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq200175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200175
  have eq200993 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq200176 (σ X0)
       grind)
    | exact superpose eq200176 eq13
    | exact resolve eq13 eq200176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201242 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq200993 X0
       have i₂ := eq200176 X0
       grind)
    | exact superpose eq200176 eq200993
    | exact resolve eq200993 eq200176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200993
  have eq202361 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 (σ X0) X1
       have i₂ := eq201242 X0
       grind)
    | exact superpose eq201242 eq8
    | exact resolve eq8 eq201242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205402 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq202361 x X0
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq202361
    | exact resolve eq202361 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202361
  have eq205662 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq205402 (σ X0)
       have i₂ := eq201242 X0
       grind)
    | exact superpose eq201242 eq205402
    | exact resolve eq205402 eq201242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205402
  have eq206719 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq205662 x
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq205662
    | exact resolve eq205662 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205662
  have eq206903 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq333 x y
       have i₂ := eq206719
       grind)
    | exact superpose eq206719 eq333
    | (have j0 := eq333 x y
       grind)
    | exact resolve eq333 eq206719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq206914 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq94711 y x
       have i₂ := eq206719
       grind)
    | exact superpose eq206719 eq94711
    | (have j0 := eq94711 y x
       grind)
    | exact resolve eq94711 eq206719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94711 eq206719
  have eq206961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq206914
       have i₂ := eq187411
       grind)
    | exact superpose eq187411 eq206914
    | exact resolve eq206914 eq187411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206914
  have eq206972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq206903
       have i₂ := eq187411
       grind)
    | exact superpose eq187411 eq206903
    | exact resolve eq206903 eq187411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206903
  have eq207005 : x = (k y y) := by
    first
    | (have r₁ := eq206961
       have r₂ := eq14
       grind)
    | exact resolve eq206961 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206961
  have eq207016 : y = (k y x) := by
    first
    | (have r₁ := eq206972
       have r₂ := eq14
       grind)
    | exact resolve eq206972 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206972
  have eq207040 : x = (M.op y y) := by
    first
    | (have i₁ := eq207005
       have i₂ := eq200176 y
       grind)
    | exact superpose eq200176 eq207005
    | exact resolve eq207005 eq200176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200176 eq207005
  have eq207195 : y = (M.op x y) := by
    first
    | (have i₁ := eq187411
       have i₂ := eq207016
       grind)
    | exact superpose eq207016 eq187411
    | exact resolve eq187411 eq207016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187411 eq207016
  have eq208081 : (M.op x (M.op x x)) = (M.op y (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq91308 y
       have i₂ := eq207040
       grind)
    | exact superpose eq207040 eq91308
    | exact resolve eq91308 eq207040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91308
  have eq208412 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq208081
       have i₂ := eq111349
       grind)
    | exact superpose eq111349 eq208081
    | exact resolve eq208081 eq111349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111349 eq208081
  have eq208579 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq208412
       have i₂ := eq207040
       grind)
    | exact superpose eq207040 eq208412
    | exact resolve eq208412 eq207040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207040 eq208412
  have eq208651 : x = y ∨ x = y := by
    first
    | (have i₁ := eq208579
       have i₂ := eq207195
       grind)
    | exact superpose eq207195 eq208579
    | exact resolve eq208579 eq207195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207195 eq208579
  have eq208652 : x = y := by grind
  clear eq208651
  have eq208683 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq208652
       grind)
    | exact superpose eq208652 eq14
    | exact resolve eq14 eq208652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208652
  have eq209573 : False := by grind
  exact eq209573
