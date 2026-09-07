import equational_theories.Definability.AutBox
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1055`: `x = x ◇ ((y ◇ (z ◇ x)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1055 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1055 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1055.models_iff G M).mp hM
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq81 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq81 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq81 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq85 (σ X0) (σ X1)
       grind)
    | exact superpose eq85 eq13
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq101
    | exact resolve eq101 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq101
  have eq929 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq106 x y
       grind)
    | exact superpose eq106 eq14
    | (have r₁ := eq14
       have r₂ := eq106 x y
       grind)
    | exact resolve eq14 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq952 : False := by grind
  exact eq952

/-- `Equation1056`: `x = x ◇ ((y ◇ (z ◇ x)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1056 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1056 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1056.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X1 (M.op x X0))
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq99 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (M.op X0 X0)
       have i₂ := eq28 X0 (σ X1)
       grind)
    | exact superpose eq28 eq48
    | exact resolve eq48 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq132 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X0) X1
       have i₂ := eq38 X2 X0
       grind)
    | exact superpose eq38 eq22
    | (have j1 := eq38 X2 X0
       grind)
    | exact resolve eq22 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq618 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq673 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq618
    | (have j0 := eq618 X0 X1
       grind)
    | exact resolve eq618 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq1474 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq133 (M.op X0 X0)
       have i₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact superpose eq28 eq133
    | (have j0 := eq133 (M.op X0 X0)
       grind)
    | exact resolve eq133 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1488 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq133 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq133
    | (have j0 := eq133 (τ X0)
       grind)
    | exact resolve eq133 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq133
  have eq1499 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1504 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1488 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1488
    | (have j0 := eq1488 X0
       grind)
    | exact resolve eq1488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1513 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1504 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1504
    | (have j0 := eq1504 X0
       grind)
    | exact resolve eq1504 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1695 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ (M.op X0 X0)) X1
       have i₂ := eq1499 X0
       grind)
    | exact superpose eq1499 eq22
    | exact resolve eq22 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1792 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1695 X0 X1
       have i₂ := eq673 X2 X0
       grind)
    | exact superpose eq673 eq1695
    | (have j1 := eq673 X2 X0
       grind)
    | exact resolve eq1695 eq673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq1695
  have eq2038 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq132 y X0 x
       grind)
    | exact superpose eq132 eq14
    | (have j1 := eq132 y X0 x
       grind)
    | exact resolve eq14 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq2075 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2038 X0
       have j1 := eq1792 y X0 x
       grind)
    | (have r₁ := eq2038 X0
       have r₂ := eq1792 y x x
       grind)
    | exact resolve eq2038 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792 eq2038
  have eq2090 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq99 (σ y) x
       have i₂ := eq2075 (σ y)
       grind)
    | exact superpose eq2075 eq99
    | exact resolve eq99 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq2112 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2075 (σ x)
       grind)
    | exact superpose eq2075 eq14
    | exact resolve eq14 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2121 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq2090 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq2090
    | exact resolve eq2090 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2262 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1513 y
       have i₂ := eq2121 y
       grind)
    | exact superpose eq2121 eq1513
    | (have j0 := eq1513 y
       grind)
    | (have r₁ := eq1513 y
       have r₂ := eq2121 y
       grind)
    | exact resolve eq1513 eq2121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq2121
  have eq2279 : y = (M.op y y) := by grind
  clear eq2262
  have eq2396 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq2279
       grind)
    | exact superpose eq2279 eq22
    | exact resolve eq22 eq2279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2279
  have eq2840 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2112
       have i₂ := eq2396 x
       grind)
    | exact superpose eq2396 eq2112
    | exact resolve eq2112 eq2396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq2396
  have eq2841 : False := by grind
  exact eq2841

/-- `Equation1060`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_pyy_pxy_Equation1060 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1060 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1060.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 (M.op x X0))
       have i₂ := eq8 X0 X0 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 (M.op X0 X0)
       have i₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq11
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq22 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq54 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq11
    | (have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq11 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq58 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
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
  have eq59 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq54 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq65 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (M.op X0 X0)
       have i₂ := eq35 X0 (τ X1)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq35
  have eq73 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq96 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq59 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq59 eq13
    | (have j1 := eq59 (σ X1) X2 X2
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq229 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq562 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1228 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq229 (τ X0)
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq229
    | (have j0 := eq229 (τ X0)
       grind)
    | exact resolve eq229 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq229
  have eq1242 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1228 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1228
    | (have j0 := eq1228 X0
       grind)
    | exact resolve eq1228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1251 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1242 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1242
    | (have j0 := eq1242 X0
       grind)
    | exact resolve eq1242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1815 : ∀ X0 X1 X2 : G, (σ X0) = (k X1 (σ X0)) ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X1 X1
       have i₂ := eq619 X0 X1
       grind)
    | exact superpose eq619 eq65
    | (have j1 := eq619 X2 X0
       grind)
    | exact resolve eq65 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq619
  have eq1893 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14
       have i₂ := eq96 x y X0
       grind)
    | exact superpose eq96 eq14
    | (have j1 := eq96 X0 y X0
       grind)
    | exact resolve eq14 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1952 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1893 X0
       have j1 := eq1815 y X0 x
       grind)
    | (have r₁ := eq1893 X0
       have r₂ := eq1815 y x x
       grind)
    | exact resolve eq1893 eq1815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq1893
  have eq1976 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1251 (σ y)
       have i₂ := eq1952 (σ y)
       grind)
    | exact superpose eq1952 eq1251
    | (have j0 := eq1251 (σ y)
       grind)
    | (have r₁ := eq1251 (σ y)
       have r₂ := eq1952 (σ y)
       grind)
    | exact resolve eq1251 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1989 : ∀ X0 : G, (τ (σ y)) = (k X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 X0 (σ y)
       have i₂ := eq1952 (σ X0)
       grind)
    | exact superpose eq1952 eq73
    | exact resolve eq73 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1952
  have eq1994 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1976
  have eq1995 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1989 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq1989
    | exact resolve eq1989 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq2115 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1251 y
       have i₂ := eq1995 y
       grind)
    | exact superpose eq1995 eq1251
    | (have j0 := eq1251 y
       grind)
    | (have r₁ := eq1251 y
       have r₂ := eq1995 y
       grind)
    | exact resolve eq1251 eq1995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq1995
  have eq2130 : y = (M.op y y) := by grind
  clear eq2115
  have eq2263 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 y X0
       have i₂ := eq2130
       grind)
    | exact superpose eq2130 eq22
    | exact resolve eq22 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq3089 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 (σ y) X0
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq22
    | exact resolve eq22 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1994
  have eq3337 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3089 (σ x)
       grind)
    | exact superpose eq3089 eq14
    | exact resolve eq14 eq3089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3345 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3337
       have i₂ := eq2263 x
       grind)
    | exact superpose eq2263 eq3337
    | exact resolve eq3337 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263 eq3337
  have eq3346 : False := by grind
  exact eq3346

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1061 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq140 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq136 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq136 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq159 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq140 (σ X0) (σ X1)
       grind)
    | exact superpose eq140 eq13
    | exact resolve eq13 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq140 X0 X1
       grind)
    | exact superpose eq140 eq159
    | exact resolve eq159 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq159
  have eq1402 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq168 x y
       grind)
    | exact superpose eq168 eq14
    | (have r₁ := eq14
       have r₂ := eq168 x y
       grind)
    | exact resolve eq14 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1427 : False := by grind
  exact eq1427

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation1076 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1076 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq86 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq86 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq86 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq90 (σ X1) (σ X0)
       grind)
    | exact superpose eq90 eq13
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 X0 X1
       have i₂ := eq90 X1 X0
       grind)
    | exact superpose eq90 eq106
    | exact resolve eq106 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq106
  have eq1720 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq113 x y
       grind)
    | exact superpose eq113 eq14
    | (have r₁ := eq14
       have r₂ := eq113 x y
       grind)
    | exact resolve eq14 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1739 : False := by grind
  exact eq1739

/-- `Equation1096`: `x = y ◇ ((x ◇ (z ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyx_y_pyy_pxy_Equation1096 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1096 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1096.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 (M.op X2 X1)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) (M.op (M.op X3 X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 X3 (M.op (M.op X0 (M.op X1 X2)) X0) X2
       have i₂ := eq8 X0 X2 X1
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8 X1 X0 (M.op X0 (M.op x X1))
       have i₂ := eq8 X0 X1 x
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X0) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X1 (M.op (M.op X0 (M.op X2 X1)) X0)
       have i₂ := eq8 X0 X1 X2
       grind)
    | exact superpose eq8 eq22
    | exact resolve eq22 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X2 (M.op X1 X0) X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X1 X0) X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq11
    | (have j0 := eq11 (M.op X1 X0) X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq22 X1 X1
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X2 X3)) (M.op X1 X0)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 (M.op X1 X0) X2 X3 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq21
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X1 (M.op X2 X3)) X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 (M.op (M.op X1 (M.op X2 X3)) X1) (M.op (M.op X0 X1) X0)
       have i₂ := eq21 X1 X2 X3 X0
       grind)
    | exact superpose eq21 eq22
    | exact resolve eq22 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq63 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq61 X0 X1 x X3
       have i₂ := eq23 X1 X3 x
       grind)
    | exact superpose eq23 eq61
    | exact resolve eq61 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq66 : ∀ X0 X1 X3 : G, (M.op (M.op X3 (M.op X1 X0)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 X0 X1 x X3
       have i₂ := eq23 (M.op X1 X0) X3 x
       grind)
    | exact superpose eq23 eq57
    | exact resolve eq57 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq105 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X1) (σ X0)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq11 (σ X0) (σ X1)
       have r₂ := eq38 X0 X1
       grind)
    | exact resolve eq11 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) (σ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq22
    | (have j1 := eq38 X1 X0
       grind)
    | exact resolve eq22 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq110 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq201 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X3 X2 X1
       have i₂ := eq63 X3 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq63 X0 (M.op X2 X1) X0
       grind)
    | exact superpose eq63 eq23
    | exact resolve eq23 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X1 X3 X2
       have i₂ := eq63 X2 X1 X0
       grind)
    | (have i₁ := eq25 X1 X1 X0
       have i₂ := eq63 X0 X1 X0
       grind)
    | exact superpose eq63 eq25
    | exact resolve eq25 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq27 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq293 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 (M.op (M.op x x) x)
       have i₂ := eq25 x (M.op x x) x
       grind)
    | exact superpose eq25 eq291
    | exact resolve eq291 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq291
  have eq321 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293 X1
       have i₂ := eq63 X1 X1 X0
       grind)
    | (have i₁ := eq293 X0
       have i₂ := eq63 X0 X0 X0
       grind)
    | exact superpose eq63 eq293
    | exact resolve eq293 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq293
  have eq1306 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq106 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq106
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1337 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq38
    | (have j0 := eq38 X0 X1
       have j1 := eq106 X1 X0
       grind)
    | exact resolve eq38 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1341 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X0)
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq11
    | (have j1 := eq106 X1 X0
       grind)
    | (have r₁ := eq11 (σ X1) (σ X1)
       have r₂ := eq106 X1 X1
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq1401 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1341 X0 X1
       have i₂ := eq13 X1 X1
       grind)
    | exact superpose eq13 eq1341
    | (have j0 := eq1341 X0 X1
       grind)
    | exact resolve eq1341 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1406 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1306 X0 X1
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq1306
    | (have j0 := eq1306 X0 X1
       grind)
    | exact resolve eq1306 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1410 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1401 X0 X1
       have j1 := eq1337 X0 X1
       grind)
    | (have r₁ := eq1401 X0 (k X1 X1)
       have r₂ := eq1337 X0 X1
       grind)
    | (have r₁ := eq1401 (k X1 X1) X0
       have r₂ := eq1337 X0 X1
       grind)
    | (have r₁ := eq1401 X0 X1
       have r₂ := eq1337 X0 X1
       grind)
    | exact resolve eq1401 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337 eq1401
  have eq1603 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ (k X0 X1))) (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (σ X0) (σ X0) x
       have i₂ := eq110 X0 X1
       grind)
    | exact superpose eq110 eq66
    | (have j1 := eq110 X1 X0
       grind)
    | exact resolve eq66 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1648 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq110 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq1649 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1648 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1800 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1649 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1649
    | exact resolve eq1649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq1649 X0
       grind)
    | exact superpose eq1649 eq22
    | exact resolve eq22 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1847 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1800 X0
       have i₂ := eq16 X0 (τ X0)
       grind)
    | exact superpose eq16 eq1800
    | exact resolve eq1800 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq1800
  have eq1850 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1847 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1847
    | exact resolve eq1847 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847
  have eq2127 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1814 X0
       have i₂ := eq1850 X0
       grind)
    | exact superpose eq1850 eq1814
    | exact resolve eq1814 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq2535 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq201 X2 (σ X0) (σ (M.op X0 X0)) X1
       have i₂ := eq2127 X0
       grind)
    | exact superpose eq2127 eq201
    | exact resolve eq201 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq6212 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1406 X0 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1406
    | exact resolve eq1406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq8666 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X1 X1)
       have i₂ := eq1410 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq1410 X0 X1
       grind)
    | exact superpose eq1410 eq9
    | (have j1 := eq1410 X0 X1
       grind)
    | exact resolve eq9 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq8897 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8666 X0 X1
       have i₂ := eq1850 X1
       grind)
    | exact superpose eq1850 eq8666
    | (have j0 := eq8666 X0 X1
       grind)
    | exact resolve eq8666 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8666
  have eq9105 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8897 X0 X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq8897
    | (have j0 := eq8897 X0 X1
       grind)
    | exact resolve eq8897 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8897
  have eq74349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq9105 x y
       grind)
    | exact superpose eq9105 eq14
    | (have j1 := eq9105 x y
       grind)
    | exact resolve eq14 eq9105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9105
  have eq78425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74349
       have i₂ := eq6212 x y
       grind)
    | exact superpose eq6212 eq74349
    | (have j1 := eq6212 x y
       grind)
    | exact resolve eq74349 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6212 eq74349
  have eq78435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq78425
  have eq78436 : x = (M.op y y) := by grind
  clear eq78435
  have eq82263 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2535 y X1 X0
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq2535
    | exact resolve eq2535 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq82319 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq204 y y X1 X0
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq204
    | exact resolve eq204 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq82340 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq321 y y
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq321
    | exact resolve eq321 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq91104 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1603 y (M.op x y) x
       have i₂ := eq82340
       grind)
    | exact superpose eq82340 eq1603
    | exact resolve eq1603 eq82340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603 eq82340
  have eq91294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq91104 x
       have i₂ := eq82263 x (σ y)
       grind)
    | exact superpose eq82263 eq91104
    | exact resolve eq91104 eq82263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82263 eq91104
  have eq91304 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq91294
       have r₂ := eq14
       grind)
    | exact resolve eq91294 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91294
  have eq99858 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq22 (σ y) (σ (M.op x y))
       have i₂ := eq91304
       grind)
    | exact superpose eq91304 eq22
    | exact resolve eq22 eq91304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq91304
  have eq99934 : (σ (M.op x y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq99858
       have i₂ := eq1649 y
       grind)
    | exact superpose eq1649 eq99858
    | exact resolve eq99858 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq99858
  have eq99958 : (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq99934
       have i₂ := eq1850 y
       grind)
    | exact superpose eq1850 eq99934
    | exact resolve eq99934 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850 eq99934
  have eq99973 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq99958
       have i₂ := eq78436
       grind)
    | exact superpose eq78436 eq99958
    | exact resolve eq99958 eq78436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78436 eq99958
  have eq100308 : (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2127 (M.op x y)
       have i₂ := eq99973
       grind)
    | exact superpose eq99973 eq2127
    | exact resolve eq2127 eq99973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq100343 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100308
       have i₂ := eq82319 x y
       grind)
    | exact superpose eq82319 eq100308
    | exact resolve eq100308 eq82319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82319 eq100308
  have eq102702 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq100343
       grind)
    | exact superpose eq100343 eq14
    | exact resolve eq14 eq100343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100343
  have eq102849 : False := by grind
  exact eq102849

/-- `Equation1112`: `x = y ◇ ((y ◇ (x ◇ y)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pyx_pxx_pyx_Equation1112 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1112 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq91 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq87 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq87 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq91 (σ X1) (σ X0)
       grind)
    | exact superpose eq91 eq13
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq91 X1 X0
       grind)
    | exact superpose eq91 eq107
    | exact resolve eq107 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq107
  have eq1505 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq14
    | (have r₁ := eq14
       have r₂ := eq114 x y
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1524 : False := by grind
  exact eq1524

/-- `Equation1137`: `x = y ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxx_pxy_pxx_pxy_Equation1137 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1137 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law1137.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  have eq8 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3)) X0) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8 (M.op (M.op (M.op X1 (M.op X2 X2)) (M.op X3 X3)) X0) X1 X2
       have i₂ := eq8 X0 (M.op X1 (M.op X2 X2)) X3
       grind)
    | exact superpose eq8 eq8
    | exact resolve eq8 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq13
    | exact resolve eq13 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq58 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq95 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq95 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq13
    | exact resolve eq13 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq115
    | exact resolve eq115 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq144 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X2)) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8 X1 (M.op X0 (M.op X2 X2)) x
       have i₂ := eq22 X1 X0 X2 x
       grind)
    | exact superpose eq22 eq8
    | exact resolve eq8 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq416 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq14
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq416
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq416
    | exact resolve eq416 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq416
  have eq436 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq435
  have eq472 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq436
       have i₂ := eq122 x y
       grind)
    | exact superpose eq122 eq436
    | exact resolve eq436 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq436
  have eq573 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq9 (M.op x y)
       have i₂ := eq472
       grind)
    | exact superpose eq472 eq9
    | exact resolve eq9 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq592 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq573
       have i₂ := eq9 (M.op x x)
       grind)
    | exact superpose eq9 eq573
    | exact resolve eq573 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq1008 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq144 x y X0
       have i₂ := eq592
       grind)
    | exact superpose eq592 eq144
    | exact resolve eq144 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1048 : x = y := by
    first
    | (have i₁ := eq1008 x
       have i₂ := eq144 x x x
       grind)
    | exact superpose eq144 eq1008
    | exact resolve eq1008 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq1008
  have eq1061 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1048
       grind)
    | exact superpose eq1048 eq14
    | exact resolve eq14 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1062 : False := by grind
  exact eq1062
