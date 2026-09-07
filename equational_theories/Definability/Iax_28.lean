import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4428`: `x ◇ (x ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pxx_pyx_Equation4428 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4428 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4428.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq15
  have eq23 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 x X2 X4 X5
       have i₂ := eq8 x X2 X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X2 X0 X0
       have i₂ := eq12 X3 X0
       grind)
    | exact superpose eq12 eq8
    | (have j1 := eq12 X3 X0
       grind)
    | exact resolve eq8 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq50 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq192 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1206 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 (M.op X1 X2))) ≠ (M.op X3 (M.op X1 X2)) ∨ (k (M.op X1 X2) X3) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 (M.op X1 X2) X3
       have i₂ := eq8 X0 (M.op X1 X2) X1 X2
       grind)
    | exact superpose eq8 eq192
    | (have j0 := eq192 (M.op X1 X2) X3
       grind)
    | exact resolve eq192 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq192 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1238 : ∀ X1 X2 X3 : G, (k (M.op X1 X2) X3) = (M.op X3 (M.op X1 X2)) := by
    intro X1 X2 X3
    first
    | (have j0 := eq1206 x X1 X2 X3
       have j1 := eq48 X3 X1 X2 (M.op X1 X2)
       grind)
    | (have r₁ := eq1206 X1 X1 X2 x
       have r₂ := eq48 x X1 (M.op X1 X2) X3
       grind)
    | exact resolve eq1206 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq1206
  have eq1271 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq14
    | (have j1 := eq52 x x
       grind)
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq13
    | exact resolve eq13 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1358 X0
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq1358
    | exact resolve eq1358 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1672 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (σ (M.op X0 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X1 X2 X3 (σ X0) (σ X0)
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq23
    | exact resolve eq23 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) X0 X1
       have i₂ := eq1224 (σ X0)
       grind)
    | exact superpose eq1224 eq19
    | exact resolve eq19 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2035 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2008 X0 X1
       have i₂ := eq1238 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq1238 eq2008
    | exact resolve eq2008 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2043 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2035 X0 X1
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq2035
    | exact resolve eq2035 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2047 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2043 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq2043
    | exact resolve eq2043 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2049 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2047 X0 X1
       have i₂ := eq1224 X0
       grind)
    | exact superpose eq1224 eq2047
    | exact resolve eq2047 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq2047
  have eq2051 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2049 X0 X1
       have i₂ := eq1238 X0 X0 X1
       grind)
    | exact superpose eq1238 eq2049
    | exact resolve eq2049 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq2049
  have eq14073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1271
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq1271
    | (have j1 := eq12 x (σ x)
       grind)
    | exact resolve eq1271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq14077 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq14073
  have eq14080 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14077
       have i₂ := eq1369 x
       grind)
    | exact superpose eq1369 eq14077
    | exact resolve eq14077 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14077
  have eq14087 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 (M.op x x)
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq9
    | exact resolve eq9 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080
  have eq14122 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14087
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq14087
    | exact resolve eq14087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14087
  have eq14123 : x = (M.op x x) := by grind
  clear eq14122
  have eq14514 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1672 x X0 X1 X2
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq1672
    | exact resolve eq1672 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq14520 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq8
    | exact resolve eq8 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14527 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1 X2 x x
       have i₂ := eq14123
       grind)
    | exact superpose eq14123 eq23
    | exact resolve eq23 eq14123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14123
  have eq14597 : ∀ X2 : G, (M.op x X2) = (M.op (σ x) X2) := by
    intro X2
    first
    | (have i₁ := eq14514 x x X2
       have i₂ := eq14527 x x X2
       grind)
    | exact superpose eq14527 eq14514
    | exact resolve eq14514 eq14527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14514 eq14527
  have eq23623 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq14597 (σ y)
       grind)
    | exact superpose eq14597 eq14
    | exact resolve eq14 eq14597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14597
  have eq42968 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14520 (σ X0) (σ X0)
       have i₂ := eq1369 X0
       grind)
    | exact superpose eq1369 eq14520
    | exact resolve eq14520 eq1369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq43408 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq42968 X0
       have i₂ := eq2051 X0 X0
       grind)
    | exact superpose eq2051 eq42968
    | exact resolve eq42968 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051 eq42968
  have eq43573 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq43408 X0
       have i₂ := eq14520 X0 X0
       grind)
    | exact superpose eq14520 eq43408
    | exact resolve eq43408 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14520 eq43408
  have eq151715 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq23623
       have i₂ := eq43573 y
       grind)
    | exact superpose eq43573 eq23623
    | (have r₁ := eq23623
       have r₂ := eq43573 y
       grind)
    | exact resolve eq23623 eq43573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23623 eq43573
  have eq151716 : False := by grind
  exact eq151716

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_y_x_pxy_Equation4430 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq8 x x X4 X5
       have i₂ := eq8 x x X0 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq8 X0 X1 x X5
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X2 X3 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq51 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq19 X2 X3 (M.op x X5) X5
       have i₂ := eq8 X0 X1 x X5
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq19 x X5 X0 X1
       grind)
    | (have i₁ := eq8 X2 X3 (M.op x X5) X5
       have i₂ := eq19 X0 X1 x X5
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28
    | exact resolve eq28 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq82 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq22 X4 x X0 X1
       grind)
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq22 X0 X1 X4 x
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X3)) = (M.op X4 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq22 X2 X3 X4 (M.op X4 x)
       have i₂ := eq8 X4 x X0 X1
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X2 (M.op X2 x) X4 X5
       have i₂ := eq22 X2 x X0 X1
       grind)
    | (have i₁ := eq8 X2 (M.op X2 x) X4 X5
       have i₂ := eq22 X0 X1 X2 x
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X2 X3) ∨ (k X2 (M.op X2 X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X2 (M.op X2 X3)
       have i₂ := eq22 X2 X3 X0 X1
       grind)
    | (have i₁ := eq11 X2 (M.op X2 X3)
       have i₂ := eq22 X0 X1 X2 X3
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 X2 (M.op X2 X3)
       grind)
    | (have r₁ := eq11 X2 (M.op X2 (M.op X2 X3))
       have r₂ := eq22 X2 (M.op X2 X3) X2 X3
       grind)
    | (have r₁ := eq11 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq22 X0 X1 X0 (M.op X0 X1)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : ∀ X0 X1 X2 X3 X4 X5 X7 : G, (M.op X3 (M.op X3 X4)) = (M.op X5 (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X7)) := by
    intro X0 X1 X2 X3 X4 X5 X7
    first
    | (have i₁ := eq83 (M.op x X7) X7 X3 X4 X5
       have i₂ := eq51 X0 X1 x X7 X2
       grind)
    | (have i₁ := eq83 (M.op X0 (M.op X0 X1)) X5 X2 X3 X4
       have i₂ := eq51 X0 X1 X2 X3 X5
       grind)
    | exact superpose eq51 eq83
    | exact resolve eq83 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1420 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq30 x y
       grind)
    | exact superpose eq30 eq14
    | (have j1 := eq30 x y
       grind)
    | exact resolve eq14 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1451 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq1473 : ∀ X0 X1 X2 X4 X5 X6 X7 : G, (M.op X5 (M.op X6 (M.op X6 X7))) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) X4) := by
    intro X0 X1 X2 X4 X5 X6 X7
    first
    | (have i₁ := eq97 X6 X7 X5 (M.op x X4) X4
       have i₂ := eq51 X0 X1 x X4 X2
       grind)
    | (have i₁ := eq97 X0 X1 X2 (M.op X0 (M.op X0 X1)) X5
       have i₂ := eq51 X0 X1 X2 x X5
       grind)
    | exact superpose eq51 eq97
    | exact resolve eq97 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1612 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X3 X4)) = (M.op (M.op (M.op X0 (M.op X1 (M.op X1 X2))) X6) X7) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq60 (M.op x X6) X6 X3 X4 X7
       have i₂ := eq97 X1 X2 X0 x X6
       grind)
    | (have i₁ := eq60 X2 (M.op X0 (M.op X0 X1)) X2 X3 x
       have i₂ := eq97 X0 X1 X2 X4 x
       grind)
    | exact superpose eq97 eq60
    | exact resolve eq60 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq97
  have eq8696 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1451 (τ X0) (τ X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq1451
    | (have j0 := eq1451 (τ X0) (τ X1)
       grind)
    | exact resolve eq1451 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1451
  have eq8703 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8696 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq8696
    | (have j0 := eq8696 X0 X1
       grind)
    | exact resolve eq8696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8696
  have eq8705 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8703 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq8703
    | (have j0 := eq8703 X0 X1
       grind)
    | exact resolve eq8703 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8703
  have eq8706 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8705 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8705
    | (have j0 := eq8705 X0 X1
       grind)
    | exact resolve eq8705 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8705
  have eq8707 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8706 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8706
    | (have j0 := eq8706 X0 X1
       grind)
    | exact resolve eq8706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8706
  have eq9048 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1 X0 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq9132 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9048 X2 (M.op X2 x)
       have i₂ := eq82 X2 x X0 X1 X2
       grind)
    | (have i₁ := eq9048 X2 x
       have i₂ := eq82 X0 X1 X2 x x
       grind)
    | exact superpose eq82 eq9048
    | exact resolve eq9048 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq9048
  have eq9331 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 X0 (M.op X1 (M.op X1 X2))
       have i₂ := eq9132 X1 X2 (σ X0)
       grind)
    | exact superpose eq9132 eq38
    | exact resolve eq38 eq9132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9334 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9331 X0 X1 X2
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq9331
    | exact resolve eq9331 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331
  have eq26832 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1420
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq1420
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq1420 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq26833 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq26832
  have eq42138 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9132 (σ x) (σ y) X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq9132
    | exact resolve eq9132 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9132
  have eq110776 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq42138 X0
       have i₂ := eq26833
       grind)
    | exact superpose eq26833 eq42138
    | exact resolve eq42138 eq26833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26833 eq42138
  have eq110799 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq110776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110776
  have eq112614 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (σ y)
       have i₂ := eq110799 (σ X0)
       grind)
    | exact superpose eq110799 eq38
    | exact resolve eq38 eq110799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq110799
  have eq112625 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112614 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq112614
    | exact resolve eq112614 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112614
  have eq112628 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq112625 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq112625
    | exact resolve eq112625 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112625
  have eq114405 : ∀ X0 : G, y ≠ X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8707 X0 y
       have i₂ := eq112628 X0
       grind)
    | exact superpose eq112628 eq8707
    | (have j0 := eq8707 X0 y
       grind)
    | (have r₁ := eq8707 y y
       have r₂ := eq112628 y
       grind)
    | exact resolve eq8707 eq112628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112628
  have eq117676 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq114405 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114405
  have eq118561 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1 y y
       have i₂ := eq117676
       grind)
    | exact superpose eq117676 eq19
    | exact resolve eq19 eq117676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq294475 : ∀ X1 : G, (M.op y y) = (M.op (M.op y y) X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq118561 (M.op x X1) X1
       have i₂ := eq118561 x X1
       grind)
    | exact superpose eq118561 eq118561
    | exact resolve eq118561 eq118561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118561
  have eq295500 : ∀ X1 : G, (M.op y y) = (M.op (M.op y y) X1) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq294475 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294475
  have eq406531 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq295500 x
       have i₂ := eq117676
       grind)
    | exact superpose eq117676 eq295500
    | exact resolve eq295500 eq117676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117676 eq295500
  have eq407179 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq406531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406531
  have eq409295 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 x x x X0 X1 y x
       have i₂ := eq407179 (M.op (M.op (M.op x (M.op x x)) x) x)
       grind)
    | exact superpose eq407179 eq1263
    | exact resolve eq1263 eq407179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq407179
  have eq411137 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq409295 X0 (M.op X0 x)
       have i₂ := eq409295 X0 x
       grind)
    | exact superpose eq409295 eq409295
    | exact resolve eq409295 eq409295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409295
  have eq412522 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq411137 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411137
  have eq414872 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq412522 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412522
  have eq414873 : y = (M.op x y) := by grind
  clear eq414872
  have eq416374 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq8 X0 X1 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq8
    | exact resolve eq8 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416383 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 x y X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq21
    | exact resolve eq21 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq416385 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq22
    | exact resolve eq22 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq416389 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 x y X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq51
    | exact resolve eq51 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq416707 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X3) X4) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1473 X1 X2 X3 X4 X0 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq1473
    | exact resolve eq1473 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq416722 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 (M.op x y)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1612 X2 x y X0 X1 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq1612
    | exact resolve eq1612 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq416766 : ∀ X0 : G, (k X0 (τ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9334 X0 x y
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq9334
    | exact resolve eq9334 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9334
  have eq416861 : ∀ X0 : G, (k X0 (τ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq416766 X0
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416766
    | exact resolve eq416766 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416766
  have eq416879 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X2 y) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq416722 X0 X1 X2 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416722
    | exact resolve eq416722 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416722
  have eq416890 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X1 X2)) X3) X4) = (M.op X0 y) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq416707 X0 X1 X2 X3 X4
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416707
    | exact resolve eq416707 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416707
  have eq417009 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416389 X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416389
    | exact resolve eq416389 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416389
  have eq417011 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
    intro X0 X1
    first
    | (have i₁ := eq416385 X0 X1
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416385
    | exact resolve eq416385 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416385
  have eq417013 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq416383 X0 X1 X2
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq416383
    | exact resolve eq416383 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416383
  have eq417017 : ∀ X2 X3 X4 : G, (M.op y y) = (M.op (M.op (M.op X2 y) X3) X4) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq416879 x x X2 X3 X4
       have i₂ := eq416374 x x
       grind)
    | exact superpose eq416374 eq416879
    | exact resolve eq416879 eq416374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416879
  have eq417028 : ∀ X0 X3 X4 : G, (M.op X0 y) = (M.op (M.op (M.op y y) X3) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq416890 X0 x x X3 X4
       have i₂ := eq416374 x x
       grind)
    | exact superpose eq416374 eq416890
    | exact resolve eq416890 eq416374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416374 eq416890
  have eq417136 : ∀ X2 : G, y = (M.op y X2) := by
    intro X2
    first
    | (have i₁ := eq417013 x x X2
       have i₂ := eq417011 x x
       grind)
    | exact superpose eq417011 eq417013
    | exact resolve eq417013 eq417011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417011 eq417013
  have eq417141 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq417028 X0 x x
       have i₂ := eq417017 y x x
       grind)
    | exact superpose eq417017 eq417028
    | exact resolve eq417028 eq417017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417017 eq417028
  have eq417191 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq417141 X0
       have i₂ := eq417136 y
       grind)
    | exact superpose eq417136 eq417141
    | exact resolve eq417141 eq417136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417141
  have eq431902 : ∀ X0 : G, (τ y) ≠ X0 ∨ (τ y) = (M.op X0 (τ y)) := by
    intro X0
    first
    | (have i₁ := eq8707 X0 (τ y)
       have i₂ := eq416861 X0
       grind)
    | exact superpose eq416861 eq8707
    | (have j0 := eq8707 X0 (τ y)
       grind)
    | (have r₁ := eq8707 (τ y) (τ y)
       have r₂ := eq416861 (τ y)
       grind)
    | exact resolve eq8707 eq416861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8707 eq416861
  have eq866962 : (τ y) = (M.op (τ y) (τ y)) := by
    first
    | (have j0 := eq431902 (τ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431902
  have eq868700 : ∀ X0 : G, (M.op y X0) = (M.op (τ y) (τ y)) := by
    intro X0
    first
    | (have i₁ := eq417009 (τ y) (τ y) X0
       have i₂ := eq866962
       grind)
    | exact superpose eq866962 eq417009
    | exact resolve eq417009 eq866962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417009
  have eq868706 : ∀ X0 : G, (τ y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq868700 X0
       have i₂ := eq866962
       grind)
    | exact superpose eq866962 eq868700
    | exact resolve eq868700 eq866962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866962 eq868700
  have eq868872 : y = (τ y) := by
    first
    | (have i₁ := eq868706 x
       have i₂ := eq417136 x
       grind)
    | exact superpose eq417136 eq868706
    | exact resolve eq868706 eq417136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417136 eq868706
  have eq870623 : y = (σ y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq868872
       grind)
    | exact superpose eq868872 eq10
    | exact resolve eq10 eq868872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868872
  have eq872866 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq870623
       grind)
    | exact superpose eq870623 eq14
    | exact resolve eq14 eq870623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872923 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq872866
       have i₂ := eq417191 (σ x)
       grind)
    | exact superpose eq417191 eq872866
    | exact resolve eq872866 eq417191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417191 eq872866
  have eq872931 : y ≠ (σ y) := by
    first
    | (have i₁ := eq872923
       have i₂ := eq414873
       grind)
    | exact superpose eq414873 eq872923
    | exact resolve eq872923 eq414873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414873 eq872923
  have eq872933 : y ≠ y := by
    first
    | (have i₁ := eq872931
       have i₂ := eq870623
       grind)
    | exact superpose eq870623 eq872931
    | (have r₁ := eq872931
       have r₂ := eq870623
       grind)
    | exact resolve eq872931 eq870623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870623 eq872931
  have eq872934 : False := by grind
  exact eq872934

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pyx_Equation4441 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4441 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq18 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X2 (M.op X0 x) X4 X5
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq8 X0 x X4 X5
       have i₂ := eq8 X0 x X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X0 X1 x x
       have i₂ := eq8 X0 X2 x x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X0 X4 X1 (M.op x (M.op X0 X1))
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
  clear eq15
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  clear eq16
  have eq66 : ∀ X0 X1 X2 X3 X5 X6 : G, (M.op (M.op X3 X5) X6) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3 X5 X6
    first
    | (have i₁ := eq8 X3 (M.op X0 x) X5 X6
       have i₂ := eq19 X0 x X3 X1 X2
       grind)
    | (have i₁ := eq8 X3 (M.op X0 x) X5 X6
       have i₂ := eq19 X0 X1 X2 x X3
       grind)
    | exact superpose eq19 eq8
    | exact resolve eq8 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X2 X3 (M.op X0 x)
       have i₂ := eq8 X0 X1 x X2
       grind)
    | exact superpose eq8 eq23
    | exact resolve eq23 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X4) X5) = (M.op X3 (M.op X6 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq18 X6 (M.op X0 x) X3 X4 X5
       have i₂ := eq19 X0 x X6 X1 X2
       grind)
    | (have i₁ := eq18 X6 (M.op X0 x) X3 X4 X5
       have i₂ := eq19 X0 X1 X2 x X6
       grind)
    | exact superpose eq19 eq18
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq285 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X0 X2) X3) ∨ (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq11 X4 (M.op (M.op X0 X2) X3)
       have i₂ := eq24 X0 X2 X3 X4 X1
       grind)
    | exact superpose eq24 eq11
    | (have j0 := eq11 X4 (M.op (M.op X0 X2) X3)
       grind)
    | exact resolve eq11 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq297 : ∀ X0 X2 X3 X4 : G, (k X4 (M.op (M.op X0 X2) X3)) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have j0 := eq285 X0 x X2 X3 X4
       grind)
    | (have r₁ := eq285 X0 x X2 X3 X4
       have r₂ := eq8 X0 x X2 X3
       grind)
    | exact resolve eq285 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq817 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq32 x y
       grind)
    | exact superpose eq32 eq14
    | (have j1 := eq32 x y
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq1698 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X3 (M.op X6 X3)) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq95 X4 (M.op X0 x) X3 X6
       have i₂ := eq18 X1 X2 X0 x X4
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1764 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X4 (M.op X0 (M.op (M.op X1 X2) X3))) = (M.op X4 (M.op X5 (M.op X6 X5))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq95 X5 X6 X4 (M.op X0 x)
       have i₂ := eq66 X1 X2 X3 X0 x X4
       grind)
    | exact superpose eq66 eq95
    | exact resolve eq95 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3567 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op X5 X6) X7) = (M.op X5 (M.op X8 (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq18 X8 (M.op X0 x) X5 X6 X7
       have i₂ := eq155 X2 X3 X4 X0 x X8 X1
       grind)
    | exact superpose eq155 eq18
    | exact resolve eq18 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7521 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq841 (τ X1) (τ X0)
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq841
    | (have j0 := eq841 (τ X1) (τ X0)
       grind)
    | exact resolve eq841 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq7528 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7521 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7521
    | (have j0 := eq7521 X0 X1
       grind)
    | exact resolve eq7521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7538 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7528 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7528
    | (have j0 := eq7528 X0 X1
       grind)
    | exact resolve eq7528 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7528
  have eq7547 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7538 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7538
    | (have j0 := eq7538 X0 X1
       grind)
    | exact resolve eq7538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7538
  have eq7548 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7547 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7547
    | (have j0 := eq7547 X0 X1
       grind)
    | exact resolve eq7547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547
  have eq12502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq817
       have i₂ := eq12 y x
       grind)
    | exact superpose eq12 eq817
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq817 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq12503 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12502
  have eq12556 : ∀ X0 X1 : G, (k X0 (M.op (σ x) X1)) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq297 (σ x) (σ y) X1 X0
       have i₂ := eq12503
       grind)
    | exact superpose eq12503 eq297
    | exact resolve eq297 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15805 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12556 X0 (σ y)
       have i₂ := eq12503
       grind)
    | exact superpose eq12503 eq12556
    | exact resolve eq12556 eq12503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503 eq12556
  have eq15840 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15805
  have eq16352 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq40 X0 (σ x)
       have i₂ := eq15840 (σ X0)
       grind)
    | exact superpose eq15840 eq40
    | exact resolve eq40 eq15840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15840
  have eq16357 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16352 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq16352
    | exact resolve eq16352 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16352
  have eq16360 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16357 X0
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq16357
    | exact resolve eq16357 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16357
  have eq16877 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7548 X0 x
       have i₂ := eq16360 X0
       grind)
    | exact superpose eq16360 eq7548
    | (have j0 := eq7548 X0 x
       grind)
    | (have r₁ := eq7548 x x
       have r₂ := eq16360 x
       grind)
    | exact resolve eq7548 eq16360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16360
  have eq21818 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq16877 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16877
  have eq22586 : ∀ X0 X1 : G, (k X0 (M.op x X1)) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq297 x y X1 X0
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq297
    | exact resolve eq297 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq22771 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq22586 X0 y
       have i₂ := eq21818
       grind)
    | exact superpose eq21818 eq22586
    | exact resolve eq22586 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21818 eq22586
  have eq22822 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq22771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22771
  have eq22972 : ∀ X0 : G, x ≠ X0 ∨ x = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7548 X0 x
       have i₂ := eq22822 X0
       grind)
    | exact superpose eq22822 eq7548
    | (have j0 := eq7548 X0 x
       grind)
    | (have r₁ := eq7548 x x
       have r₂ := eq22822 x
       grind)
    | exact resolve eq7548 eq22822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7548 eq22822
  have eq36435 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq22972 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22972
  have eq36436 : x = (M.op x x) := by grind
  clear eq36435
  have eq37788 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq11
    | (have j0 := eq11 x x
       grind)
    | (have r₁ := eq11 x x
       have r₂ := eq36436
       grind)
    | exact resolve eq11 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37810 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 x x X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq95
    | exact resolve eq95 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq37895 : x = (k x x) := by grind
  clear eq37788
  have eq37913 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq37810 X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq37810
    | exact resolve eq37810 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37810
  have eq39335 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq841 x x
       have i₂ := eq37895
       grind)
    | exact superpose eq37895 eq841
    | (have j0 := eq841 x x
       grind)
    | exact resolve eq841 eq37895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841 eq37895
  have eq39339 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq39335
  have eq54212 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) X0 (σ x)
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq23
    | exact resolve eq23 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq54309 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 (M.op X3 (M.op (σ x) (σ x))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1698 X3 (σ x) (σ x) X0 X2 X1
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq1698
    | exact resolve eq1698 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq54310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1764 X1 X2 X3 X4 X0 (σ x) (σ x)
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq1764
    | exact resolve eq1764 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq54342 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X3) X4))) = (M.op X0 (σ x)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq54310 X0 X1 X2 X3 X4
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54310
    | exact resolve eq54310 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54310
  have eq54343 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 (M.op X3 (σ x)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq54309 X0 X1 X2 X3
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54309
    | exact resolve eq54309 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54309
  have eq54367 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54212 X0
       have i₂ := eq39339
       grind)
    | exact superpose eq39339 eq54212
    | exact resolve eq54212 eq39339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39339 eq54212
  have eq54385 : ∀ X0 X2 X3 : G, (M.op X0 x) = (M.op X0 (M.op X2 (M.op X3 (σ x)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq54343 X0 x X2 X3
       have i₂ := eq37913 X0 x
       grind)
    | exact superpose eq37913 eq54343
    | exact resolve eq54343 eq37913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54343
  have eq54397 : (σ x) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq54367 x
       have i₂ := eq37913 (σ x) x
       grind)
    | exact superpose eq37913 eq54367
    | exact resolve eq54367 eq37913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37913 eq54367
  have eq54536 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X4 X5) X6))))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq3567 X2 X3 X4 X5 X6 x x X0 X1
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq3567
    | exact resolve eq3567 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq56227 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op x (M.op X1 (M.op X2 (σ x)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54536 X0 X1 X2 x x x x
       have i₂ := eq54342 X2 x x x x
       grind)
    | exact superpose eq54342 eq54536
    | exact resolve eq54536 eq54342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54342 eq54536
  have eq56284 : ∀ X0 : G, (M.op x X0) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq56227 X0 x x
       have i₂ := eq54385 x x x
       grind)
    | exact superpose eq54385 eq56227
    | exact resolve eq56227 eq54385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54385 eq56227
  have eq56327 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq56284 X0
       have i₂ := eq36436
       grind)
    | exact superpose eq36436 eq56284
    | exact resolve eq56284 eq36436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36436 eq56284
  have eq56701 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq155 x x x X0 X1 X2 x
       have i₂ := eq56327 (M.op (M.op x x) x)
       grind)
    | exact superpose eq56327 eq155
    | exact resolve eq155 eq56327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq102333 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq56701 (σ x) x x
       have i₂ := eq54397
       grind)
    | exact superpose eq54397 eq56701
    | exact resolve eq56701 eq54397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54397 eq56701
  have eq103992 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq102333 (σ y)
       grind)
    | exact superpose eq102333 eq14
    | exact resolve eq14 eq102333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102333
  have eq104609 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq103992
       have i₂ := eq56327 y
       grind)
    | exact superpose eq56327 eq103992
    | exact resolve eq103992 eq56327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56327 eq103992
  have eq104610 : False := by grind
  exact eq104610

/-- `Equation4444`: `x ◇ (y ◇ x) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_x_pxy_Equation4444 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4444 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4444.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq17 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X1 X0 X3
       have i₂ := eq8 X1 X0 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op X1 X0) X0 X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 (M.op X1 X0) X2
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X2 X1 (M.op X0 (M.op X1 X2))
       have i₂ := eq8 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X1 X2 x
       have i₂ := eq21 X0 X1 X0 x
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X0 X1 X2 X3
       have i₂ := eq8 X1 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq8 eq19
    | exact resolve eq19 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq15
    | (have j1 := eq12 (τ X0) X1
       grind)
    | exact resolve eq15 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29
    | exact resolve eq29 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq72 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X1 X0 X3
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq21
    | exact resolve eq21 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X3 X4 X5 : G, (M.op X4 (M.op X3 X4)) = (M.op (M.op X0 (M.op X1 X0)) X5) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq21 (M.op x (M.op X1 X0)) X3 X4 X5
       have i₂ := eq21 x X1 X0 (M.op X3 X4)
       grind)
    | exact superpose eq21 eq21
    | exact resolve eq21 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X4 (M.op X3 X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq76 X4 X3 X1 X0 x
       have i₂ := eq21 X4 X3 X4 x
       grind)
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq76
  have eq154 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq17 X2 X3 (M.op X0 (M.op X1 X0)) X4
       have i₂ := eq24 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq24 eq17
    | exact resolve eq17 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8 X1 X0 X4
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq8
    | exact resolve eq8 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op (M.op X1 X0) X2) ∨ (k X3 (M.op (M.op X1 X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 X3 (M.op (M.op X1 X0) X2)
       have i₂ := eq25 X1 X0 X2 X3
       grind)
    | exact superpose eq25 eq11
    | (have j0 := eq11 X3 (M.op (M.op X1 X0) X2)
       grind)
    | exact resolve eq11 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq236 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X0) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq230 X0 X1 X2 X3
       grind)
    | (have r₁ := eq230 X0 X1 X2 X3
       have r₂ := eq8 X0 X1 X2
       grind)
    | exact resolve eq230 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq273 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 x x (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq24 X0 X1 (M.op x x)
       grind)
    | exact superpose eq24 eq236
    | exact resolve eq236 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 (M.op X2 X1))
       have i₂ := eq273 X1 X2 (τ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq400 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq31
    | (have j0 := eq31 X1 X0
       have j1 := eq31 X1 X0
       grind)
    | exact resolve eq31 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X0 X1
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) X2) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 (σ X0) (σ X1) X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq8
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq8 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq31 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq31 X0 X1
       grind)
    | exact resolve eq11 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (σ X0) X3) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17 (σ X1) (σ X0) X2 X3
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq17
    | (have j1 := eq31 X1 X0
       grind)
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq31 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq426 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq424
    | (have j0 := eq424 X0 X1
       grind)
    | exact resolve eq424 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq428 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq402
    | (have j0 := eq402 X0 X1
       grind)
    | exact resolve eq402 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq661 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X1)) = (M.op (σ X0) X4) ∨ (M.op (σ X3) (σ X0)) = (σ (k X3 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq154 X1 X2 (σ X0) (σ X3) X4
       have i₂ := eq31 X3 X0
       grind)
    | exact superpose eq31 eq154
    | (have j1 := eq31 X3 X0
       grind)
    | exact resolve eq154 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq154
  have eq6896 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) ≠ (σ (M.op (M.op X0 X1) X2)) ∨ (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op (M.op X0 X1) X2)) (σ (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423 (M.op (M.op X0 X1) X2)
       have i₂ := eq236 X1 X0 X2 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq236 eq423
    | (have j0 := eq423 (M.op (M.op X0 X1) X2)
       grind)
    | exact resolve eq423 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq423
  have eq6931 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X2)) = (M.op (σ (M.op (M.op X0 X1) X2)) (σ (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6896 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6896
  have eq6982 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq7042 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6982 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq6982
    | (have j0 := eq6982 X0 X1
       grind)
    | exact resolve eq6982 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6982
  have eq9318 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq426 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq426
    | exact resolve eq426 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq9400 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9318 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9318
    | (have j0 := eq9318 X0 X1
       grind)
    | exact resolve eq9318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318
  have eq9402 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9400 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9400
    | (have j0 := eq9400 X0 X1
       grind)
    | exact resolve eq9400 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400
  have eq10348 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (M.op (σ X1) X4) = (M.op (σ X1) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq111 X2 X3 (σ X0) (σ X1)
       have i₂ := eq414 X1 X0 X4 X5
       grind)
    | exact superpose eq414 eq111
    | (have j1 := eq414 X1 X1 X4 X5
       grind)
    | exact resolve eq111 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq11111 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9402 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9402
    | exact resolve eq9402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9402
  have eq11455 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11111 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11638 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11455 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq72 X0 X1 X2 X3
       grind)
    | exact superpose eq72 eq11455
    | (have j0 := eq11455 (M.op (M.op X0 X1) X2) X3
       grind)
    | (have r₁ := eq11455 (M.op (M.op X0 X1) X2) X3
       have r₂ := eq72 X0 X1 X2 X3
       grind)
    | exact resolve eq11455 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq11651 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq11638 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11638
  have eq12223 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) X2) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq412 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq15592 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq428 (τ X0) (τ X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq428
    | (have j0 := eq428 (τ X0) (τ X1)
       grind)
    | exact resolve eq428 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq15626 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15592 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq15592
    | (have j0 := eq15592 X0 X1
       grind)
    | exact resolve eq15592 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15592
  have eq15642 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15626 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15626
    | (have j0 := eq15626 X0 X1
       grind)
    | exact resolve eq15626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626
  have eq15655 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15642 X0 X1
       have i₂ := eq16 X0 (τ X1)
       grind)
    | exact superpose eq16 eq15642
    | (have j0 := eq15642 X0 X1
       grind)
    | exact resolve eq15642 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15642
  have eq15664 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15655 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15655
    | (have j0 := eq15655 X0 X1
       grind)
    | exact resolve eq15655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655
  have eq15671 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15664 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15664
    | (have j0 := eq15664 X0 X1
       grind)
    | exact resolve eq15664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15672 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15671 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15671
    | (have j0 := eq15671 X0 X1
       grind)
    | exact resolve eq15671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15671
  have eq15673 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15672 X0 X1
       have j1 := eq11455 X1 X0
       grind)
    | (have r₁ := eq15672 X1 X0
       have r₂ := eq11455 X0 X1
       grind)
    | (have r₁ := eq15672 X0 X1
       have r₂ := eq11455 X0 X1
       grind)
    | exact resolve eq15672 eq11455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15672
  have eq20759 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq400 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq400
    | exact resolve eq400 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq20897 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20759 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq20759
    | (have j0 := eq20759 X0 X1
       grind)
    | exact resolve eq20759 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq20759
  have eq20899 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20897 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20897
    | (have j0 := eq20897 X0 X1
       grind)
    | exact resolve eq20897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq20897
  have eq20901 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq20899 X0 X1
       have j1 := eq11 X0 (σ X1)
       grind)
    | (have r₁ := eq20899 X0 X1
       have r₂ := eq11 X0 (σ X1)
       grind)
    | exact resolve eq20899 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20899
  have eq20971 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (σ X1)
       have i₂ := eq20901 (σ X0) X1
       grind)
    | exact superpose eq20901 eq39
    | (have j1 := eq20901 (σ X0) X1
       grind)
    | exact resolve eq39 eq20901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq20901
  have eq21066 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20971 X0 X1
       have i₂ := eq9 X1
       grind)
    | exact superpose eq9 eq20971
    | (have j0 := eq20971 X0 X1
       grind)
    | exact resolve eq20971 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20971
  have eq21089 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X1) (σ X0)) = (k (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21066 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq21066
    | (have j0 := eq21066 X0 X1
       grind)
    | exact resolve eq21066 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21066
  have eq21097 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21089 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq21089
    | (have j0 := eq21089 X0 X1
       grind)
    | exact resolve eq21089 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21089
  have eq23208 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq21097 y x
       grind)
    | exact superpose eq21097 eq14
    | (have j1 := eq21097 y x
       grind)
    | exact resolve eq14 eq21097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq23566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq23208
       have i₂ := eq7042 x y
       grind)
    | exact superpose eq7042 eq23208
    | (have j1 := eq7042 x y
       grind)
    | (have r₁ := eq23208
       have r₂ := eq7042 x y
       grind)
    | exact resolve eq23208 eq7042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7042 eq23208
  have eq23567 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq23566
  have eq23570 : y = (k y x) := by
    first
    | (have j1 := eq11455 y x
       grind)
    | (have r₁ := eq23567
       have r₂ := eq11455 y x
       grind)
    | exact resolve eq23567 eq11455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11455 eq23567
  have eq23728 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25141 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17 y x x x
       have i₂ := eq23728
       grind)
    | exact superpose eq23728 eq17
    | exact resolve eq17 eq23728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28477 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq23728
       have i₂ := eq25141 x X0
       grind)
    | (have i₁ := eq23728
       have i₂ := eq25141 X0 x
       grind)
    | exact superpose eq25141 eq23728
    | exact resolve eq23728 eq25141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23728 eq25141
  have eq28637 : ∀ X0 : G, y = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq28477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28477
  have eq29525 : ∀ X1 : G, y = (M.op X1 y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq24 y X1 x
       have i₂ := eq28637 (M.op X1 y)
       grind)
    | exact superpose eq28637 eq24
    | exact resolve eq24 eq28637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28637
  have eq30711 : ∀ X0 X1 : G, (k X0 (M.op y x)) = X0 ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq273 y x X0
       have i₂ := eq29525 X1
       grind)
    | exact superpose eq29525 eq273
    | (have j1 := eq29525 X1
       grind)
    | exact resolve eq273 eq29525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq29525
  have eq33017 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X1)) X2) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12223 (τ X0) (τ X1) X2
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12223
    | (have j0 := eq12223 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq12223 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12223
  have eq33131 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33017 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33017
    | (have j0 := eq33017 X0 X1 X2
       grind)
    | exact resolve eq33017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33017
  have eq33155 : ∀ X0 X1 X2 : G, (k X0 X1) ≠ (M.op X1 X2) ∨ (M.op (σ (τ X1)) X2) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33131 X0 X1 X2
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33131
    | (have j0 := eq33131 X0 X1 X2
       grind)
    | exact resolve eq33131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33131
  have eq33168 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33155 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33155
    | (have j0 := eq33155 X0 X1 X2
       grind)
    | exact resolve eq33155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33155
  have eq33171 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X2) ∨ (k X0 X1) ≠ (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33168 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33168
    | (have j0 := eq33168 X0 X1 X2
       grind)
    | exact resolve eq33168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33168
  have eq37931 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op X3 X2)) = (M.op (σ X1) (σ (k X0 X1))) ∨ (M.op X4 (M.op X5 X4)) = (M.op (σ X1) X6) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq111 X2 X3 (σ X0) (σ X1)
       have i₂ := eq661 X1 X4 X5 X0 X6
       grind)
    | exact superpose eq661 eq111
    | (have j1 := eq661 X1 X2 X3 X3 (σ (k X0 X1))
       grind)
    | exact resolve eq111 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq46960 : ∀ X2 X3 : G, y = (k y X2) ∨ (k X3 (M.op y x)) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq11651 x x y X3
       have i₂ := eq30711 x (M.op x x)
       grind)
    | exact superpose eq30711 eq11651
    | (have j1 := eq30711 X3 x
       grind)
    | exact resolve eq11651 eq30711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30711
  have eq81188 : y ≠ y ∨ y = (k y (M.op y x)) := by
    first
    | (have j0 := eq46960 (M.op y x) y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46960
  have eq81189 : y = (k y (M.op y x)) := by grind
  clear eq81188
  have eq81742 : y ≠ y ∨ (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq15673 y (M.op y x)
       have i₂ := eq81189
       grind)
    | exact superpose eq81189 eq15673
    | (have j0 := eq15673 y (M.op y x)
       grind)
    | (have r₁ := eq15673 y (M.op y x)
       have r₂ := eq81189
       grind)
    | exact resolve eq15673 eq81189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15673 eq81189
  have eq81748 : (M.op y x) = (k (M.op y x) y) := by grind
  clear eq81742
  have eq82733 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op y x) = (k (M.op y x) y) := by
    first
    | (have i₁ := eq81748
       have i₂ := eq11111 y (M.op y x)
       grind)
    | exact superpose eq11111 eq81748
    | (have j1 := eq11111 y (M.op y x)
       grind)
    | exact resolve eq81748 eq11111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11111 eq81748
  have eq82767 : (M.op y x) = (M.op (M.op y x) y) := by
    first
    | (have j1 := eq33171 (M.op y x) y x
       grind)
    | (have r₁ := eq82733
       have r₂ := eq33171 (M.op y x) y x
       grind)
    | exact resolve eq82733 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33171 eq82733
  have eq82768 : (M.op y x) = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq82767
       have i₂ := eq8 x y y
       grind)
    | exact superpose eq8 eq82767
    | exact resolve eq82767 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82767
  have eq83774 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq24 x y x
       have i₂ := eq82768
       grind)
    | exact superpose eq82768 eq24
    | exact resolve eq24 eq82768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq83777 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X0 X1 y x
       have i₂ := eq82768
       grind)
    | exact superpose eq82768 eq111
    | exact resolve eq111 eq82768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq82768
  have eq86907 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op y x) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq210 X0 X1 x (M.op y x) X3
       have i₂ := eq83774 (M.op (M.op X0 X1) x)
       grind)
    | exact superpose eq83774 eq210
    | exact resolve eq210 eq83774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq83774
  have eq95140 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 X3)) ≠ (M.op (σ X0) X2) ∨ (M.op X3 (M.op X4 X3)) = (M.op (σ X0) (σ (k X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq10348 X1 X0 X3 X4 X4 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10348
  have eq95142 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X4 X3)) = (M.op (σ X0) (σ (k X1 X0))) := by
    intro X0 X1 X3 X4
    first
    | (have j0 := eq95140 X0 X1 x X3 X4
       have j1 := eq37931 X1 X0 X3 X4 X3 X4 (σ (k X1 X0))
       grind)
    | (have r₁ := eq95140 X1 X1 (σ (k X0 X1)) x X3
       have r₂ := eq37931 X0 X1 x X3 X4 x x
       grind)
    | (have r₁ := eq95140 X1 X1 x X4 x
       have r₂ := eq37931 X0 X1 x X3 X4 x x
       grind)
    | (have r₁ := eq95140 X0 X1 (M.op x (σ X0)) (σ X1) X4
       have r₂ := eq37931 X0 X1 x X3 (σ X0) x (M.op X4 (σ X1))
       grind)
    | exact resolve eq95140 eq37931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37931 eq95140
  have eq95916 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X1 X0))) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq95142 X0 X1 x x
       have i₂ := eq83777 x x
       grind)
    | exact superpose eq83777 eq95142
    | exact resolve eq95142 eq83777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95142
  have eq109053 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ (k X0 X1)))) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq95916 (τ X1) (τ X0)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq95916
    | exact resolve eq95916 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq109066 : (M.op (σ x) (σ y)) = (M.op y x) := by
    first
    | (have i₁ := eq95916 x y
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq95916
    | exact resolve eq95916 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95916
  have eq109407 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (k X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq109053 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq109053
    | exact resolve eq109053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109053
  have eq109452 : ∀ X0 X1 : G, (M.op X1 (k X0 X1)) = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq109407 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq109407
    | exact resolve eq109407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109407
  have eq110225 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (M.op X2 X1))) X0) = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109452 X0 (σ (M.op X1 (M.op X2 X1)))
       have i₂ := eq329 X0 X1 X2
       grind)
    | exact superpose eq329 eq109452
    | exact resolve eq109452 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq110261 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op y x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq109452 (M.op (M.op X0 X1) X2) X3
       have i₂ := eq11651 X0 X1 X2 X3
       grind)
    | exact superpose eq11651 eq109452
    | exact resolve eq109452 eq11651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11651
  have eq110295 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109452 y x
       have i₂ := eq23570
       grind)
    | exact superpose eq23570 eq109452
    | exact resolve eq109452 eq23570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23570 eq109452
  have eq110769 : ∀ X0 X1 X2 X3 : G, (M.op x y) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110261 X0 X1 X2 X3
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110261
    | exact resolve eq110261 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110261
  have eq110797 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (σ (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110225 X0 X1 X2
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110225
    | exact resolve eq110225 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110225
  have eq110803 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op y x)) := by
    intro X3
    first
    | (have i₁ := eq110769 x x x X3
       have i₂ := eq86907 x x x
       grind)
    | exact superpose eq86907 eq110769
    | exact resolve eq110769 eq86907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86907 eq110769
  have eq110823 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op y x)) X0) := by
    intro X0
    first
    | (have i₁ := eq110797 X0 x x
       have i₂ := eq83777 x x
       grind)
    | exact superpose eq83777 eq110797
    | exact resolve eq110797 eq83777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83777 eq110797
  have eq110827 : ∀ X3 : G, (M.op x y) = (M.op X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq110803 X3
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110803
    | exact resolve eq110803 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110803
  have eq110847 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq110823 X0
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq110823
    | exact resolve eq110823 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110823
  have eq114754 : (σ (M.op x y)) ≠ (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq109066
       grind)
    | exact superpose eq109066 eq14
    | exact resolve eq14 eq109066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109066
  have eq114971 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq114754
       have i₂ := eq110295
       grind)
    | exact superpose eq110295 eq114754
    | exact resolve eq114754 eq110295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110295 eq114754
  have eq119027 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq6931 x x (M.op x y)
       have i₂ := eq110827 (M.op x x)
       grind)
    | exact superpose eq110827 eq6931
    | exact resolve eq6931 eq110827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6931 eq110827
  have eq119207 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq119027
       have i₂ := eq110847 (σ (M.op x y))
       grind)
    | exact superpose eq110847 eq119027
    | exact resolve eq119027 eq110847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110847 eq119027
  have eq119256 : False := by grind
  exact eq119256

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
