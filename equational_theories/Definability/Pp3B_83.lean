import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxy_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : (M.op x y) = (M.op x y) := by grind
  have eq18 : (M.op x y) = (M.op x y) := by grind
  clear eq17
  have eq19 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq19
  have eq21 : (σ x) = (σ x) := by grind
  have eq22 : (σ x) = (σ x) := by grind
  clear eq21
  have eq23 : (σ y) = (σ y) := by grind
  have eq24 : (σ y) = (σ y) := by grind
  clear eq23
  have eq25 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq25
  have eq27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq124 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq209 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq53 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X0 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq53 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X1 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq234 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq234 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq234 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq236 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56 eq231
    | exact resolve eq231 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq270 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq56
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq274 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq270
    | exact resolve eq270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq276 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq274
    | exact resolve eq274 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq278 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq276
    | exact resolve eq276 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq282 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq124 X0 X0
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq124
    | exact resolve eq124 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq283 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq235 (σ X0)
       grind)
    | exact superpose eq235 eq15
    | exact resolve eq15 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq283
    | exact resolve eq283 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq285 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq235 (τ X0)
       grind)
    | exact superpose eq235 eq282
    | exact resolve eq282 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq282
  have eq294 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) = (σ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq284 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq284 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq284
    | exact resolve eq284 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X0
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq294
    | exact resolve eq294 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq961 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq52 X1 X4 x x
       have i₂ := eq52 X1 X0 x x
       grind)
    | (have i₁ := eq52 X0 X1 x x
       have i₂ := eq52 X0 (M.op x x) x x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq966 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X5 X2) X5 X3 X4
       have i₂ := eq52 X2 X5 X0 X1
       grind)
    | (have i₁ := eq52 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq52 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq52 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1028 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq961 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq961
    | (have j0 := eq961 X0 y x
       grind)
    | exact resolve eq961 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1029 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq961
    | (have j0 := eq961 X0 (σ y) (σ x)
       grind)
    | exact resolve eq961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y (M.op X0 X0) X0
       have i₂ := eq1028 (M.op X0 X0)
       grind)
    | exact superpose eq1028 eq9
    | exact resolve eq9 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1077 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq961 X0 (M.op X0 y) X1
       have i₂ := eq1028 X0
       grind)
    | (have i₁ := eq961 x (M.op x y) x
       have i₂ := eq1028 X0
       grind)
    | exact superpose eq1028 eq961
    | exact resolve eq961 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1029 eq9
    | exact resolve eq9 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1121 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq1072 (M.op X1 X1)
       have i₂ := eq53 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq53 eq1072
    | exact resolve eq1072 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1158 : ∀ X0 X1 : G, (M.op X1 y) = (M.op (M.op X0 X0) (M.op X1 (M.op x (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq979 X1 (M.op X1 y) X0
       have i₂ := eq1028 X1
       grind)
    | (have i₁ := eq979 x (M.op x y) x
       have i₂ := eq1028 X0
       grind)
    | exact superpose eq1028 eq979
    | exact resolve eq979 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1208 : ∀ X0 X1 : G, (M.op X1 (M.op x (M.op x y))) = (M.op X1 (M.op X0 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1077 X1 X1
       have i₂ := eq961 X1 y X0
       grind)
    | (have i₁ := eq1077 X1 X1
       have i₂ := eq961 X0 y X1
       grind)
    | exact superpose eq961 eq1077
    | exact resolve eq1077 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1760 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (M.op x (M.op x y)) y) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1158 eq9
    | exact resolve eq9 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1765 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op x (M.op x y)) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq1158 eq53
    | exact resolve eq53 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1767 : (M.op (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y))))) = (σ (M.op (M.op x (M.op x y)) y)) := by
    first
    | exact superpose eq1158 eq284
    | exact resolve eq284 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1769 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1158 eq979
    | exact resolve eq979 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1786 : (σ (M.op (M.op x (M.op x y)) y)) = (M.op (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq1767
       have i₂ := eq284 (M.op x sF0)
       grind)
    | exact superpose eq284 eq1767
    | exact resolve eq1767 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1790 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 X1
       have i₂ := eq1765 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact superpose eq1765 eq306
    | exact resolve eq306 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq1800 : (σ (M.op (M.op x (M.op x y)) y)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) := by
    first
    | (have i₁ := eq1786
       have i₂ := eq1765 (σ (M.op x sF0)) (M.op (σ (M.op x sF0)) (σ (M.op x sF0)))
       grind)
    | exact superpose eq1765 eq1786
    | exact resolve eq1786 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq2341 : ∀ X0 : G, (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) = (σ (M.op (M.op x (M.op x y)) (M.op X0 (M.op X0 y)))) := by
    intro X0
    first
    | exact superpose eq1208 eq284
    | exact resolve eq284 eq1208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq3309 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op (M.op x (M.op x y)) y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1760 eq979
    | exact resolve eq979 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3311 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op (M.op (M.op x (M.op x y)) y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1760 eq961
    | exact resolve eq961 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq3342 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) X1) = (M.op (M.op (M.op (M.op x (M.op x y)) y) (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1765 (M.op X0 X0) X1
       have i₂ := eq1765 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1765 eq1765
    | exact resolve eq1765 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3550 : ∀ X0 : G, (M.op (σ (M.op (M.op x (M.op x y)) y)) (σ (M.op (M.op x (M.op x y)) y))) = (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) := by
    intro X0
    first
    | exact superpose eq1765 eq284
    | exact resolve eq284 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3562 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1765 eq1121
    | exact resolve eq1121 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq3672 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq1800 eq3550
    | exact resolve eq3550 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3550
  have eq3889 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op (M.op x (M.op x y)) y) (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq3342 eq3672
    | exact resolve eq3672 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342 eq3672
  have eq3915 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op x (M.op x y)) y) X0)) = (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1760 eq1769
    | exact resolve eq1769 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760 eq1769
  have eq8361 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1765 eq209
    | exact resolve eq209 eq1765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8371 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq209 y (M.op y y) X0 X1
       have i₂ := eq1077 y (M.op y y)
       grind)
    | exact superpose eq1077 eq209
    | exact resolve eq209 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq9308 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 (M.op (M.op x (M.op x y)) y))) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1077 eq8371
    | exact resolve eq8371 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq9415 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq8371 x X0
       grind)
    | exact superpose eq8371 eq9
    | exact resolve eq9 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9420 : ∀ X0 : G, (M.op (M.op (M.op x (M.op x y)) y) X0) = (M.op (M.op y (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq1765 x X0
       have i₂ := eq8371 x X0
       grind)
    | exact superpose eq8371 eq1765
    | exact resolve eq1765 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765
  have eq9426 : ∀ X0 X1 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1 x
       have i₂ := eq8371 x (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq8371 eq979
    | exact resolve eq979 eq8371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8371
  have eq10078 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq9420 eq3309
    | exact resolve eq3309 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq10079 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq9420 eq3311
    | exact resolve eq3311 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq10100 : ∀ X0 X1 : G, (M.op (M.op (M.op x (M.op x y)) y) (M.op X1 X0)) = (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq9420 eq3915
    | exact resolve eq3915 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq10189 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op (M.op x (M.op x y)) y) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq9420 eq3889
    | exact resolve eq3889 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3889
  have eq10198 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | exact superpose eq9420 eq1790
    | exact resolve eq1790 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq10199 : (σ (M.op (M.op x (M.op x y)) y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y))))) := by
    first
    | exact superpose eq9420 eq1800
    | exact resolve eq1800 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq10513 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x (M.op x y)) y))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op y (M.op x (M.op x y))) (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq9420 eq10189
    | exact resolve eq10189 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10189
  have eq10548 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y (M.op x (M.op x y))) X0)) = (M.op (M.op y (M.op x (M.op x y))) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq9420 eq10100
    | exact resolve eq10100 eq9420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9420 eq10100
  have eq13625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq278
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq278
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13625
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13625
    | exact resolve eq13625 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13625
  have eq13646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq13643
    | exact resolve eq13643 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13643
  have eq13647 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13646
       have r₂ := eq27
       grind)
    | exact resolve eq13646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13646
  have eq13648 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13647
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13647
    | exact resolve eq13647 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13647
  have eq13649 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13648
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13648
    | exact resolve eq13648 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13648
  have eq13650 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13649 eq236
    | (have r₁ := eq236
       have r₂ := eq13649
       grind)
    | exact resolve eq236 eq13649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq13649
  have eq13702 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13650
  have eq13703 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13702
  have eq23388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13703
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq13703
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq13703 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13703
  have eq23412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23388
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23388
    | exact resolve eq23388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23388
  have eq23415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq23412
    | exact resolve eq23412 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23412
  have eq23416 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23415
       have r₂ := eq27
       grind)
    | exact resolve eq23415 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23415
  have eq23417 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23416
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23416
    | exact resolve eq23416 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23416
  have eq23418 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq23417
  have eq23419 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23418
    | exact resolve eq23418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23418
  have eq23420 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23419
  have eq23421 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq230
       have i₂ := eq23420
       grind)
    | exact superpose eq23420 eq230
    | (have r₁ := eq230
       have r₂ := eq23420
       grind)
    | exact resolve eq230 eq23420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq23432 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq284 x
       have i₂ := eq23420
       grind)
    | exact superpose eq23420 eq284
    | exact resolve eq284 eq23420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23420
  have eq23499 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23421
  have eq23500 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23499
  have eq23504 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23432
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23432
    | exact resolve eq23432 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23432
  have eq23506 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23504
    | exact resolve eq23504 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23504
  have eq24053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq278
       have i₂ := eq23500
       grind)
    | exact superpose eq23500 eq278
    | exact resolve eq278 eq23500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq23500
  have eq24063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq24053
  have eq24065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq24063
    | exact resolve eq24063 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24063
  have eq24067 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24065
       have r₂ := eq27
       grind)
    | exact resolve eq24065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065
  have eq24191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24067 eq23506
    | exact resolve eq23506 eq24067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23506 eq24067
  have eq24276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24191
  have eq24291 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq24276
       have r₂ := eq27
       grind)
    | exact resolve eq24276 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24276
  have eq24297 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24291 eq1100
    | exact resolve eq1100 eq24291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100 eq24291
  have eq24874 : (τ (σ y)) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24297 eq285
    | exact resolve eq285 eq24297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24297
  have eq24972 : (τ (σ y)) = (M.op (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24874
       have i₂ := eq285 sF2
       grind)
    | exact superpose eq285 eq24874
    | exact resolve eq24874 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq24874
  have eq25004 : (τ (σ y)) = (M.op (τ (σ x)) (M.op (M.op y (M.op x (M.op x y))) (τ (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24972
       have i₂ := eq10078 (τ sF2) (τ sF2) (τ sF2)
       grind)
    | exact superpose eq10078 eq24972
    | exact resolve eq24972 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10078 eq24972
  have eq25023 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10548 eq25004
    | exact resolve eq25004 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25004
  have eq25025 : (τ (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq25023
    | exact resolve eq25023 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq25023
  have eq25026 : (τ (σ y)) = (M.op x (M.op (M.op y (M.op x (M.op x y))) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10548 eq25025
    | exact resolve eq25025 eq10548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10548 eq25025
  have eq25027 : y = (M.op x (M.op (M.op y (M.op x (M.op x y))) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq25026
    | exact resolve eq25026 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq25026
  have eq29342 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X5 X5) X0)) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) (M.op (M.op y (M.op x (M.op x y))) X0))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq9415 eq967
    | exact resolve eq967 eq9415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29382 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op X0 X1)) = (M.op (M.op X2 X2) (M.op (M.op X3 X3) (M.op X4 (M.op X0 (M.op (M.op X5 X5) X1))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq967 x x (M.op X0 (M.op (M.op X5 X5) X1)) X2 X3 X4
       have i₂ := eq966 X1 x x X0 X5
       grind)
    | exact superpose eq966 eq967
    | exact resolve eq967 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29501 : ∀ X0 X1 X2 X3 X4 X5 X6 X8 : G, (M.op X6 (M.op (M.op X8 X8) (M.op X0 X3))) = (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op X6 (M.op X0 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X8
    first
    | (have i₁ := eq966 (M.op (M.op X8 X8) (M.op X0 X3)) X4 X5 X6 x
       have i₂ := eq967 X1 X2 X3 x X8 X0
       grind)
    | (have i₁ := eq966 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X2 X3 X4
       have i₂ := eq967 X0 X1 X2 X3 X4 (M.op X4 X4)
       grind)
    | exact superpose eq967 eq966
    | exact resolve eq966 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq30230 : ∀ X0 X2 X3 X6 X8 : G, (M.op X6 (M.op (M.op X8 X8) (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op (M.op X2 X2) X3))) := by
    intro X0 X2 X3 X6 X8
    first
    | (have i₁ := eq29501 X0 x X2 X3 x x X6 X8
       have i₂ := eq29382 X0 (M.op (M.op X2 X2) X3) x x X6 x
       grind)
    | exact superpose eq29382 eq29501
    | exact resolve eq29501 eq29382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29382 eq29501
  have eq30268 : ∀ X0 X3 X5 : G, (M.op X3 (M.op (M.op y (M.op x (M.op x y))) X0)) = (M.op X3 (M.op (M.op X5 X5) X0)) := by
    intro X0 X3 X5
    first
    | (have i₁ := eq29342 X0 x x X3 x X5
       have i₂ := eq966 (M.op (M.op y (M.op x sF0)) X0) x x X3 x
       grind)
    | exact superpose eq966 eq29342
    | exact resolve eq29342 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq29342
  have eq42344 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25027 eq9415
    | exact resolve eq9415 eq25027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9415 eq25027
  have eq42376 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42344
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42344
    | exact resolve eq42344 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42344
  have eq42377 : x = (M.op x y) := by grind
  clear eq42376
  have eq42384 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq42377 eq20
    | exact resolve eq20 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq42621 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op X0 (M.op X0 y)))) := by
    intro X0
    first
    | exact superpose eq42377 eq2341
    | exact resolve eq2341 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341
  have eq42676 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (M.op x x) y))) (M.op x x)) := by
    intro X0 X1
    first
    | exact superpose eq42377 eq3562
    | exact resolve eq3562 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3562
  have eq42899 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op (M.op x x) y))) X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq42377 eq8361
    | exact resolve eq8361 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8361
  have eq42906 : ∀ X0 X1 : G, (M.op (M.op y (M.op x x)) X1) = (M.op (M.op X0 (M.op X0 (M.op (M.op x x) y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq42377 eq9308
    | exact resolve eq9308 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308
  have eq42919 : ∀ X0 X1 : G, (M.op (M.op y (M.op x x)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq42377 eq9426
    | exact resolve eq9426 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9426
  have eq42963 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op (M.op y (M.op x x)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq42377 eq10079
    | exact resolve eq10079 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10079
  have eq43005 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op y (M.op x x)) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | exact superpose eq42377 eq10198
    | exact resolve eq10198 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10198
  have eq43006 : (σ (M.op (M.op x x) y)) = (M.op (M.op y (M.op x x)) (M.op (σ (M.op x x)) (σ (M.op x x)))) := by
    first
    | exact superpose eq42377 eq10199
    | exact resolve eq10199 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10199
  have eq43021 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x x) y))) = (M.op (M.op y (M.op x x)) (M.op (M.op y (M.op x x)) (M.op (σ (M.op x x)) (σ (M.op x x))))) := by
    intro X0
    first
    | exact superpose eq42377 eq10513
    | exact resolve eq10513 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq43429 : ∀ X0 X3 X5 : G, (M.op X3 (M.op (M.op X5 X5) X0)) = (M.op X3 (M.op (M.op y (M.op x x)) X0)) := by
    intro X0 X3 X5
    first
    | exact superpose eq42377 eq30268
    | exact resolve eq30268 eq42377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30268 eq42377
  have eq43693 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op (M.op x x) y))) = (M.op (M.op y (M.op x x)) (M.op (M.op y (M.op x x)) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq43021 X0
       have i₂ := eq284 x
       grind)
    | exact superpose eq284 eq43021
    | exact resolve eq43021 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43021
  have eq43701 : (σ (M.op (M.op x x) y)) = (M.op (M.op y (M.op x x)) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq43006
       have i₂ := eq284 x
       grind)
    | exact superpose eq284 eq43006
    | exact resolve eq43006 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43006
  have eq43708 : ∀ X1 : G, (M.op (M.op y (M.op x x)) X1) = (M.op y X1) := by
    intro X1
    first
    | (have i₁ := eq42906 x X1
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq42906
    | exact resolve eq42906 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42906
  have eq43710 : ∀ X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op y X2) := by
    intro X1 X2
    first
    | (have i₁ := eq42899 x X1 X2 x
       have i₂ := eq220 x x x y
       grind)
    | exact superpose eq220 eq42899
    | exact resolve eq42899 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42899
  have eq43756 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq42676 x x
       have i₂ := eq220 x x x y
       grind)
    | exact superpose eq220 eq42676
    | exact resolve eq42676 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq42676
  have eq43765 : (σ y) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq42621 x
       have i₂ := eq979 x y x
       grind)
    | exact superpose eq979 eq42621
    | exact resolve eq42621 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq42621
  have eq43835 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq42384
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq42384
    | exact resolve eq42384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42384
  have eq43892 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op (M.op X0 X0) (M.op (M.op x x) y))) := by
    intro X0
    first
    | (have i₁ := eq43693 X0
       have i₂ := eq9 (M.op (σ x) (σ x)) (M.op y (M.op x x)) (σ x)
       grind)
    | exact superpose eq9 eq43693
    | exact resolve eq43693 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43693
  have eq43895 : (σ (M.op (M.op x x) y)) = (M.op (M.op y (M.op x x)) (M.op (M.op y (M.op x x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq43701
       have i₂ := eq43429 (M.op (σ x) (σ x)) (M.op y (M.op x x)) (σ x)
       grind)
    | exact superpose eq43429 eq43701
    | exact resolve eq43701 eq43429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43429 eq43701
  have eq43920 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42963 X0 X1 X2
       have i₂ := eq43708 X0
       grind)
    | exact superpose eq43708 eq42963
    | exact resolve eq42963 eq43708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42963
  have eq44014 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq42919 X0 X1
       have i₂ := eq43708 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq43708 eq42919
    | exact resolve eq42919 eq43708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42919
  have eq44190 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op y (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43005 X0 X1
       have i₂ := eq43708 (M.op (σ X1) (σ X1))
       grind)
    | exact superpose eq43708 eq43005
    | exact resolve eq43005 eq43708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43005 eq43708
  have eq44403 : ∀ X0 X3 X6 X8 : G, (M.op X6 (M.op (M.op X8 X8) (M.op X0 X3))) = (M.op X6 (M.op X0 (M.op y X3))) := by
    intro X0 X3 X6 X8
    first
    | (have i₁ := eq30230 X0 x X3 X6 X8
       have i₂ := eq43710 x X3
       grind)
    | exact superpose eq43710 eq30230
    | exact resolve eq30230 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30230
  have eq44830 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq43765
       have i₂ := eq284 x
       grind)
    | exact superpose eq284 eq43765
    | exact resolve eq43765 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43765
  have eq44870 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43835 eq22
    | exact resolve eq22 eq43835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq44871 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43835 eq26
    | exact resolve eq26 eq43835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq43835
  have eq45443 : (M.op (σ x) (σ x)) = (σ (M.op y (M.op (M.op x x) y))) := by
    first
    | (have i₁ := eq43892 x
       have i₂ := eq43710 x (M.op (M.op x x) y)
       grind)
    | exact superpose eq43710 eq43892
    | exact resolve eq43892 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43892
  have eq45446 : (σ (M.op (M.op x x) y)) = (M.op y (M.op y (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq43895
       have i₂ := eq43756
       grind)
    | exact superpose eq43756 eq43895
    | exact resolve eq43895 eq43756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43756 eq43895
  have eq45474 : ∀ X1 : G, (M.op y (M.op (σ X1) (σ X1))) = (σ (M.op y (M.op X1 X1))) := by
    intro X1
    first
    | (have i₁ := eq44190 x X1
       have i₂ := eq43710 x (M.op X1 X1)
       grind)
    | exact superpose eq43710 eq44190
    | exact resolve eq44190 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44190
  have eq46133 : ∀ X0 X3 X6 : G, (M.op X6 (M.op X0 (M.op y X3))) = (M.op X6 (M.op y (M.op X0 X3))) := by
    intro X0 X3 X6
    first
    | (have i₁ := eq44403 X0 X3 X6 x
       have i₂ := eq43710 x (M.op X0 X3)
       grind)
    | exact superpose eq43710 eq44403
    | exact resolve eq44403 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44403
  have eq46327 : (σ y) = (M.op y (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq44830
       have i₂ := eq43710 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact superpose eq43710 eq44830
    | exact resolve eq44830 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44830
  have eq46607 : (M.op (σ x) (σ x)) = (σ (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq45443
       have i₂ := eq43710 x y
       grind)
    | exact superpose eq43710 eq45443
    | exact resolve eq45443 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45443
  have eq46610 : (σ (M.op (M.op x x) y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq45446
       have i₂ := eq44870
       grind)
    | exact superpose eq44870 eq45446
    | exact resolve eq45446 eq44870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45446
  have eq47363 : (σ y) = (M.op y (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq46327
       have i₂ := eq44870
       grind)
    | exact superpose eq44870 eq46327
    | exact resolve eq46327 eq44870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46327
  have eq47591 : (M.op (σ x) (σ x)) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq46607
       have i₂ := eq45474 y
       grind)
    | exact superpose eq45474 eq46607
    | exact resolve eq46607 eq45474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45474 eq46607
  have eq47594 : (σ (M.op y y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq46610
       have i₂ := eq43710 x y
       grind)
    | exact superpose eq43710 eq46610
    | exact resolve eq46610 eq43710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43710 eq46610
  have eq48038 : (σ y) = (M.op y (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq47363
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47363
    | exact resolve eq47363 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47363
  have eq48114 : (M.op (σ x) (σ x)) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq47591
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47591
    | exact resolve eq47591 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47591
  have eq48117 : (M.op (σ y) (σ y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))) := by
    first
    | (have i₁ := eq47594
       have i₂ := eq284 y
       grind)
    | exact superpose eq284 eq47594
    | exact resolve eq47594 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq47594
  have eq48427 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq48114
       have i₂ := eq44870
       grind)
    | exact superpose eq44870 eq48114
    | exact resolve eq48114 eq44870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44870 eq48114
  have eq48429 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
    first
    | exact superpose eq48038 eq48117
    | exact resolve eq48117 eq48038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48038 eq48117
  have eq48624 : (M.op (σ y) (σ y)) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq48429
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48429
    | exact resolve eq48429 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq48429
  have eq48780 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op y (M.op y (σ y))) := by
    first
    | exact superpose eq48624 eq48427
    | exact resolve eq48427 eq48624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48427 eq48624
  have eq49789 : (σ (M.op x y)) = (M.op y (M.op (σ (M.op x y)) (M.op y (M.op y (σ y))))) := by
    first
    | exact superpose eq48780 eq44014
    | exact resolve eq44014 eq48780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44014 eq48780
  have eq49793 : (σ (M.op x y)) = (M.op y (M.op y (M.op (σ (M.op x y)) (M.op y (σ y))))) := by
    first
    | (have i₁ := eq49789
       have i₂ := eq46133 sF1 (M.op y sF3) y
       grind)
    | exact superpose eq46133 eq49789
    | exact resolve eq49789 eq46133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46133 eq49789
  have eq49801 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq49793
       have i₂ := eq43920 sF3 sF1 y
       grind)
    | exact superpose eq43920 eq49793
    | exact resolve eq49793 eq43920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43920 eq49793
  have eq49805 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44871 eq49801
    | exact resolve eq49801 eq44871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44871 eq49801
  have eq49809 : False := by grind
  exact eq49809

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq196 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq196 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact resolve eq196 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1334 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq199
  have eq1380 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1927 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1380 (σ X1) (σ X0)
       grind)
    | exact superpose eq1380 eq15
    | exact resolve eq15 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1940 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1927 X0 X1
       have i₂ := eq1380 X1 X0
       grind)
    | exact superpose eq1380 eq1927
    | exact resolve eq1927 eq1380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380 eq1927
  have eq1952 : False := by grind
  exact eq1952

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq71 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq617 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq659 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq617 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq617
    | (have j0 := eq617 x y X0
       grind)
    | exact resolve eq617 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq716 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 X0) X0
       have i₂ := eq659 (M.op X0 X0)
       grind)
    | exact superpose eq659 eq14
    | exact resolve eq14 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq800 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq10512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10512
    | exact resolve eq10512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10512
  have eq10524 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10513
       have r₂ := eq28
       grind)
    | exact resolve eq10513 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq10526 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10524
    | exact resolve eq10524 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10524
  have eq10709 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10526
  have eq10757 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10709
    | exact resolve eq10709 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10709
  have eq10763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10757 eq109
    | exact resolve eq109 eq10757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10757
  have eq10771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10763
  have eq10773 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10771
       have r₂ := eq28
       grind)
    | exact resolve eq10771 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10771
  have eq10910 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq10773
  have eq10958 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10910
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq10910
    | exact resolve eq10910 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10910
  have eq10961 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq10958
       grind)
    | exact superpose eq10958 eq68
    | exact resolve eq68 eq10958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10958
  have eq10975 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10961
    | exact resolve eq10961 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961
  have eq11132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10975 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11132
    | exact resolve eq11132 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132
  have eq11146 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11135
       have r₂ := eq28
       grind)
    | exact resolve eq11135 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11135
  have eq11148 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11146
    | exact resolve eq11146 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11146
  have eq11149 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11148
  have eq11153 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11149
  have eq11201 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11153
    | exact resolve eq11153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11153
  have eq11314 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11201 eq10975
    | exact resolve eq10975 eq11201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10975 eq11201
  have eq11316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11314
  have eq11320 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11316
       have r₂ := eq28
       grind)
    | exact resolve eq11316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11316
  have eq11323 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11320 eq72
    | (have r₁ := eq72
       have r₂ := eq11320
       grind)
    | exact resolve eq72 eq11320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq11324 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11320 eq28
    | exact resolve eq28 eq11320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11320
  have eq11325 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11323
  have eq20419 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11325 eq109
    | exact resolve eq109 eq11325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20436 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq20419
  have eq20450 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20436
       have r₂ := eq11324
       grind)
    | exact resolve eq20436 eq11324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20436
  have eq20568 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq20450
  have eq20665 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20568
    | exact resolve eq20568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20568
  have eq21136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20665 eq109
    | exact resolve eq109 eq20665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq20665
  have eq21149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq21136
  have eq21153 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21149
       have r₂ := eq28
       grind)
    | exact resolve eq21149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21149
  have eq21157 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq21153
  have eq21254 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21157
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21157
    | exact resolve eq21157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21157
  have eq21557 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq21254
       grind)
    | exact superpose eq21254 eq68
    | exact resolve eq68 eq21254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21254
  have eq21573 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq21557
    | exact resolve eq21557 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21557
  have eq21670 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21573 eq11325
    | exact resolve eq11325 eq21573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq21675 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21670
  have eq21683 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21675
       have r₂ := eq11324
       grind)
    | exact resolve eq21675 eq11324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324 eq21675
  have eq21700 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq21683
  have eq21797 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq21700
    | exact resolve eq21700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21700
  have eq22076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21797 eq21573
    | exact resolve eq21573 eq21797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21573 eq21797
  have eq22079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq22076
  have eq22087 : y = (M.op x y) := by
    first
    | (have r₁ := eq22079
       have r₂ := eq28
       grind)
    | exact resolve eq22079 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22079
  have eq22090 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22087 eq21
    | exact resolve eq21 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq22095 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq22087 eq71
    | (have r₁ := eq71
       have r₂ := eq22087
       grind)
    | exact resolve eq71 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq22143 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22087 eq716
    | exact resolve eq716 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq22144 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq22095
  have eq22145 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq22143 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22143
    | (have j0 := eq22143 X0
       grind)
    | exact resolve eq22143 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22143
  have eq22196 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq22090
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22090
    | exact resolve eq22090 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22090
  have eq22197 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq22087 eq22145
    | exact resolve eq22145 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22145
  have eq22198 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq22196 eq27
    | exact resolve eq27 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq24024 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq22144
       grind)
    | exact superpose eq22144 eq68
    | exact resolve eq68 eq22144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq24034 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq800 x y
       have i₂ := eq22144
       grind)
    | exact superpose eq22144 eq800
    | (have j0 := eq800 x y
       grind)
    | exact resolve eq800 eq22144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22144
  have eq24037 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq24034
  have eq24044 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24037
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24037
    | exact resolve eq24037 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24037
  have eq24052 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22196 eq24024
    | exact resolve eq24024 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24024
  have eq24054 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22196 eq24044
    | exact resolve eq24044 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24044
  have eq24062 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24052
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24052
    | exact resolve eq24052 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24052
  have eq24063 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24054
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24054
    | exact resolve eq24054 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24054
  have eq24069 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22196 eq24062
    | exact resolve eq24062 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq24070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22198 eq24063
    | exact resolve eq24063 eq22198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24063
  have eq24071 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24070
       have r₂ := eq28
       grind)
    | exact resolve eq24070 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24070
  have eq24072 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24071
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24071
    | exact resolve eq24071 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24071
  have eq24073 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24072
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24072
    | exact resolve eq24072 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24072
  have eq24074 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22196 eq24073
    | exact resolve eq24073 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24073
  have eq24132 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq24074
  have eq24226 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22198 eq24132
    | exact resolve eq24132 eq22198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24132
  have eq24275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24226 eq24069
    | exact resolve eq24069 eq24226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24069 eq24226
  have eq24278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq24275
  have eq24280 : y = (M.op x x) := by
    first
    | (have r₁ := eq24278
       have r₂ := eq28
       grind)
    | exact resolve eq24278 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24278
  have eq24295 : (M.op x y) = (k y x) := by grind
  have eq24368 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq635 x x X0
       have i₂ := eq24280
       grind)
    | exact superpose eq24280 eq635
    | exact resolve eq635 eq24280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq24280
  have eq24373 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq24368 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24368
    | (have j0 := eq24368 X0
       grind)
    | exact resolve eq24368 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24368
  have eq24392 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq24295
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24295
    | exact resolve eq24295 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24295
  have eq24396 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | exact superpose eq22087 eq24373
    | exact resolve eq24373 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24373
  have eq24409 : y = (k y x) := by
    first
    | exact superpose eq22087 eq24392
    | exact resolve eq24392 eq22087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22087 eq24392
  have eq24413 : x = y := by
    first
    | (have i₁ := eq24396 x
       have i₂ := eq22197 x
       grind)
    | exact superpose eq22197 eq24396
    | exact resolve eq24396 eq22197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22197 eq24396
  have eq24660 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq24413
       grind)
    | exact superpose eq24413 eq25
    | exact resolve eq25 eq24413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq24793 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq22196 eq24660
    | exact resolve eq24660 eq22196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22196 eq24660
  have eq24853 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24793
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24793
    | exact resolve eq24793 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24793
  have eq24953 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24853 eq22198
    | exact resolve eq22198 eq24853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22198
  have eq25089 : x = (k x x) := by
    first
    | (have i₁ := eq24409
       have i₂ := eq24413
       grind)
    | exact superpose eq24413 eq24409
    | exact resolve eq24409 eq24413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24409 eq24413
  have eq25116 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq800 x x
       have i₂ := eq25089
       grind)
    | exact superpose eq25089 eq800
    | (have j0 := eq800 x x
       grind)
    | exact resolve eq800 eq25089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq25089
  have eq25119 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25116
  have eq25120 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq25119
  have eq25127 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25120
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25120
    | exact resolve eq25120 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25120
  have eq25148 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24853 eq25127
    | exact resolve eq25127 eq24853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24853 eq25127
  have eq25396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25148 eq24953
    | exact resolve eq24953 eq25148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24953 eq25148
  have eq25397 : False := by grind
  exact eq25397

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op X1 X1) X2
       have i₂ := eq25 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq25 X3 (M.op X1 X1) X2
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq25 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X0 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq25 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X1 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq69 X1 (τ X0)
       grind)
    | exact superpose eq69 eq19
    | (have j1 := eq69 X1 (τ X0)
       grind)
    | exact resolve eq19 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq69 (σ X1) (σ X0)
       grind)
    | exact superpose eq69 eq15
    | (have j1 := eq69 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq69 (τ X1) X0
       grind)
    | exact superpose eq69 eq18
    | (have j1 := eq69 (τ X1) X0
       grind)
    | exact resolve eq18 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq69
  have eq132 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq24 X1 X4 x x
       have i₂ := eq24 X1 X0 x x
       grind)
    | (have i₁ := eq24 X0 X1 x x
       have i₂ := eq24 X0 (M.op x x) x x
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq24 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq24 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X3) X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq132 X1 (M.op X2 (M.op (M.op X3 X3) X0)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq132
    | exact resolve eq132 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq152 X2 X3 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq152 X2 X3 (M.op X1 X1)
       have i₂ := eq25 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq25 eq152
    | exact resolve eq152 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq274 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X3) X0)) = (M.op (M.op X1 X1) (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq152 X2 (M.op X2 (M.op (M.op X3 X3) X0)) X1
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq152
    | exact resolve eq152 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X2) = (M.op (M.op X3 X3) (M.op X4 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq152 X4 (M.op X4 X2) X3
       have i₂ := eq24 X2 X4 X0 X1
       grind)
    | (have i₁ := eq152 (M.op X2 X2) (M.op (M.op X3 X3) X0) X2
       have i₂ := eq24 X0 X1 X2 X3
       grind)
    | exact superpose eq24 eq152
    | exact resolve eq152 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1)) = (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X1 (M.op (M.op X4 X4) (M.op X5 X5)) X2 X3
       have i₂ := eq91 X4 X5 X0 X1
       grind)
    | (have i₁ := eq24 X3 (M.op X2 X2) X2 X3
       have i₂ := eq91 X0 X1 X2 X3
       grind)
    | exact superpose eq91 eq24
    | exact resolve eq24 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq889 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X2)) (M.op (M.op X4 X4) X5))) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq108 X3 (M.op X2 X2) X4 X5
       have i₂ := eq91 X0 X1 X2 (M.op X2 X2)
       grind)
    | (have i₁ := eq108 X0 (M.op (M.op X0 X0) (M.op X1 X1)) X2 X3
       have i₂ := eq91 X0 X1 X2 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq91 eq108
    | exact resolve eq108 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1667 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1702 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1667 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1667
    | (have j0 := eq1667 X0 X1
       grind)
    | exact resolve eq1667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1749 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ (M.op (τ X1) (M.op (M.op X2 X2) X0))) X1) ∨ (τ X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112 X0 (M.op (τ X0) (M.op (M.op X2 X2) X0))
       have i₂ := eq9 X0 (τ X0) X2
       grind)
    | exact superpose eq9 eq112
    | exact resolve eq112 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq1826 : ∀ X0 X1 : G, (k (σ (M.op (τ X1) (τ X1))) X1) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1
       have i₂ := eq132 (τ X1) (τ X1) X0
       grind)
    | (have i₁ := eq34 X1
       have i₂ := eq132 X0 (τ X1) (τ X1)
       grind)
    | exact superpose eq132 eq34
    | exact resolve eq34 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1907 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114 x y
       grind)
    | exact superpose eq114 eq16
    | (have j1 := eq114 x y
       grind)
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq6172 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq273 x x X0 X2
       have i₂ := eq274 (M.op X0 X2) (M.op x x) X0 X1
       grind)
    | (have i₁ := eq273 X0 X1 (M.op x x) x
       have i₂ := eq274 (M.op (M.op x x) x) X1 (M.op (M.op X0 X0) (M.op X1 X1)) x
       grind)
    | exact superpose eq274 eq273
    | exact resolve eq273 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq6842 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6172 X2 x X3
       have i₂ := eq91 X0 X1 x (M.op X2 X3)
       grind)
    | (have i₁ := eq6172 X0 (M.op X1 X1) X2
       have i₂ := eq91 X1 X1 X2 (M.op X0 X2)
       grind)
    | exact superpose eq91 eq6172
    | exact resolve eq6172 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq23957 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (τ (σ X1))))) = (σ (k (M.op (τ (σ X1)) (τ (σ X1))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op (τ (σ X1)) (τ (σ X1))) X1
       have i₂ := eq1826 X0 (σ X1)
       grind)
    | exact superpose eq1826 eq15
    | exact resolve eq15 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23980 : ∀ X0 X1 X2 : G, (σ (k (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) X2)) = (k (σ (M.op X0 (M.op X0 (τ (σ X1))))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op (τ (σ X1)) (τ (σ X1)))) X1 X2
       have i₂ := eq1826 X0 (σ X1)
       grind)
    | exact superpose eq1826 eq22
    | exact resolve eq22 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq23982 : ∀ X0 X1 : G, (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) = (τ (σ (M.op X0 (M.op X0 (τ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X1)) (τ (σ X1)))) X1
       have i₂ := eq1826 X0 (σ X1)
       grind)
    | exact superpose eq1826 eq23
    | exact resolve eq23 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq24031 : ∀ X0 X1 : G, (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) = (M.op X0 (M.op X0 (τ (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23982 X0 X1
       have i₂ := eq10 (M.op X0 (M.op X0 (τ (σ X1))))
       grind)
    | exact superpose eq10 eq23982
    | exact resolve eq23982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23982
  have eq24033 : ∀ X0 X1 X2 : G, (σ (k (k (τ (σ (M.op (τ (σ X1)) (τ (σ X1))))) X1) X2)) = (σ (k (M.op X0 (M.op X0 (τ (σ X1)))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23980 X0 X1 X2
       have i₂ := eq15 (M.op X0 (M.op X0 (τ (σ X1)))) X2
       grind)
    | exact superpose eq15 eq23980
    | exact resolve eq23980 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23980
  have eq24045 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (k (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23957 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23957
    | exact resolve eq23957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23957
  have eq24063 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (τ (σ (M.op X1 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24031 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24031
    | exact resolve eq24031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24031
  have eq24065 : ∀ X0 X1 X2 : G, (σ (k (k (τ (σ (M.op X1 X1))) X1) X2)) = (σ (k (M.op X0 (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24033 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24033
    | exact resolve eq24033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24033
  have eq24074 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq24045
  have eq24081 : ∀ X0 X1 : G, (k (M.op X1 X1) X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24063 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq24063
    | exact resolve eq24063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24063
  have eq24083 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 (M.op X0 X1)) X2)) = (σ (k (k (M.op X1 X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24065 X0 X1 X2
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq24065
    | exact resolve eq24065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24065
  have eq24087 : ∀ X0 X1 X2 : G, (σ (k (M.op X0 (M.op X0 X1)) X2)) = (σ (k (M.op X1 (M.op X1 X1)) X2)) := by
    intro X0 X1 X2
    grind
  clear eq24083
  have eq24275 : ∀ X0 X1 : G, (k (τ (M.op (σ X1) (σ X1))) X1) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X1) (σ X1)) X1
       have i₂ := eq24081 X0 (σ X1)
       grind)
    | exact superpose eq24081 eq23
    | exact resolve eq23 eq24081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25698 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (σ (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24074 X0 X1
       have i₂ := eq24074 X2 X1
       grind)
    | (have i₁ := eq24074 X0 X1
       have i₂ := eq24074 X1 X1
       grind)
    | exact superpose eq24074 eq24074
    | exact resolve eq24074 eq24074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24074
  have eq27238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1907
       have i₂ := eq1702 y x
       grind)
    | exact superpose eq1702 eq1907
    | (have j1 := eq1702 (σ y) (σ x)
       grind)
    | (have r₁ := eq1907
       have r₂ := eq1702 y x
       grind)
    | exact resolve eq1907 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702 eq1907
  have eq27239 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq27238
  have eq27252 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq152 (σ x) (σ y) X0
       have i₂ := eq27239
       grind)
    | exact superpose eq27239 eq152
    | exact resolve eq152 eq27239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq27239
  have eq27570 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X1)) (M.op (M.op X2 X2) X0)))) X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X1)) (M.op (M.op X2 X2) X0))) X1
       have i₂ := eq1749 X0 (σ X1) X2
       grind)
    | exact superpose eq1749 eq23
    | (have j1 := eq1749 (k (τ (σ (M.op (τ (σ X1)) (M.op (M.op X2 X2) X0)))) X1) (σ X0) X2
       grind)
    | exact resolve eq23 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1749
  have eq27579 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (τ (σ X1)) (M.op (M.op X2 X2) X0)) X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27570 X0 X1 X2
       have i₂ := eq10 (M.op (τ (σ X1)) (M.op (M.op X2 X2) X0))
       grind)
    | exact superpose eq10 eq27570
    | (have j0 := eq27570 (k (M.op (τ (σ X1)) (M.op (M.op X2 X2) X0)) X1) X0 X2
       grind)
    | exact resolve eq27570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27570
  have eq27614 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27579 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq27579
    | (have j0 := eq27579 (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) X0 X2
       grind)
    | exact resolve eq27579 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27579
  have eq27632 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27614 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27614
    | (have j0 := eq27614 X0 X1 X2
       grind)
    | exact resolve eq27614 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27614
  have eq27637 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op (M.op X2 X2) X0)) X1) = X0 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27632 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq27632
    | (have j0 := eq27632 X0 X1 X2
       grind)
    | exact resolve eq27632 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27632
  have eq27720 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X3 X0)) = (k (M.op X1 X0) X1) ∨ (M.op X3 (M.op X3 X0)) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq27637 (M.op X3 (M.op X3 X0)) X1 (M.op x x)
       have i₂ := eq273 x x X3 X0
       grind)
    | exact superpose eq273 eq27637
    | (have j0 := eq27637 (M.op X3 (M.op X3 X0)) (k (M.op X1 X0) X1) x
       grind)
    | exact resolve eq27637 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq27637
  have eq76241 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ (τ X1))))) = (τ (k (M.op (σ (τ X1)) (σ (τ X1))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (M.op (σ (τ X1)) (σ (τ X1)))
       have i₂ := eq24275 X0 (τ X1)
       grind)
    | exact superpose eq24275 eq35
    | exact resolve eq35 eq24275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24275
  have eq76314 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (k (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76241 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76241
    | exact resolve eq76241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76241
  have eq76351 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X1))) = (τ (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq76314
  have eq79418 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op X0 X0) X1)) = (τ (M.op (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1)) (M.op (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1)) (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq76351 (M.op X0 X0) (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1))
       have i₂ := eq278 X2 X3 X1 X0 (M.op X0 X0)
       grind)
    | exact superpose eq278 eq76351
    | exact resolve eq76351 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq76351
  have eq79781 : ∀ X0 X1 X3 : G, (τ (M.op (M.op X0 X0) X1)) = (τ (M.op (M.op X3 X3) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq79418 X0 X1 x X3
       have i₂ := eq9 (M.op (M.op X3 X3) X1) (M.op (M.op x x) (M.op (M.op X3 X3) X1)) x
       grind)
    | exact superpose eq9 eq79418
    | exact resolve eq79418 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79418
  have eq112942 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X1)) X2) = (τ (σ (k (M.op X0 (M.op X0 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (M.op X1 (M.op X1 X1)) X2)
       have i₂ := eq24087 X0 X1 X2
       grind)
    | (have i₁ := eq10 (k (M.op X0 (M.op X0 X1)) X2)
       have i₂ := eq24087 X0 X1 X2
       grind)
    | exact superpose eq24087 eq10
    | exact resolve eq10 eq24087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24087
  have eq112995 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) X2) = (k (M.op X1 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112942 X0 X1 X2
       have i₂ := eq10 (k (M.op X0 (M.op X0 X1)) X2)
       grind)
    | exact superpose eq10 eq112942
    | exact resolve eq112942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112942
  have eq115112 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X0 X1)) X2) = (k (M.op X3 (M.op X3 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112995 X0 X1 X2
       have i₂ := eq112995 X3 X1 X2
       grind)
    | (have i₁ := eq112995 X0 X1 X2
       have i₂ := eq112995 X1 X1 X2
       grind)
    | exact superpose eq112995 eq112995
    | exact resolve eq112995 eq112995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112995
  have eq154697 : ∀ X0 : G, (τ (σ y)) = (τ (M.op (M.op X0 X0) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq79781 X0 (M.op (σ x) (σ x)) x
       have i₂ := eq27252 x
       grind)
    | exact superpose eq27252 eq79781
    | exact resolve eq79781 eq27252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27252 eq79781
  have eq155150 : ∀ X0 : G, y = (τ (M.op (M.op X0 X0) (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq154697 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq154697
    | exact resolve eq154697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154697
  have eq657306 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X1)) = (k (M.op X0 X1) X0) ∨ (M.op X3 (M.op X3 X1)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq132 X2 X1 X3
       have i₂ := eq27720 X1 X0 X3
       grind)
    | exact superpose eq27720 eq132
    | (have j1 := eq27720 X1 X0 X2
       grind)
    | exact resolve eq132 eq27720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27720
  have eq826202 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X4 (M.op X4 (M.op (M.op X3 X3) X2))) = (k (M.op X0 (M.op (M.op X3 X3) X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq186 X2 X1 X1 X3
       have i₂ := eq657306 X0 (M.op (M.op X3 X3) X2) X4 X1
       grind)
    | (have i₁ := eq186 X0 X1 X2 X3
       have i₂ := eq657306 (M.op X1 (M.op X2 (M.op (M.op X3 X3) X0))) X1 X2 X3
       grind)
    | exact superpose eq657306 eq186
    | (have j1 := eq657306 X0 (M.op (M.op X3 X3) X2) X4 X3
       grind)
    | exact resolve eq186 eq657306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq657306
  have eq827459 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op (M.op X3 X3) X2)) X0) = X2 ∨ (M.op X1 X0) = (M.op X1 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq826202 X0 X1 X2 X3 x
       have i₂ := eq9 X2 x X3
       grind)
    | exact superpose eq9 eq826202
    | (have j0 := eq826202 X0 X1 X2 X3 x
       grind)
    | exact resolve eq826202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826202
  have eq1047112 : ∀ X0 X1 X3 : G, (M.op X3 X1) = (M.op X3 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq827459 X1 X3 (M.op X1 X0) (M.op x x)
       have i₂ := eq6842 x x X1 X0
       grind)
    | exact superpose eq6842 eq827459
    | (have j0 := eq827459 X1 X3 (M.op X1 X0) X3
       grind)
    | exact resolve eq827459 eq6842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6842 eq827459
  have eq1059593 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 X2)) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X1 X2 X0
       have i₂ := eq1047112 X2 X0 X0
       grind)
    | exact superpose eq1047112 eq132
    | (have j1 := eq1047112 X2 X0 x
       grind)
    | exact resolve eq132 eq1047112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq1061441 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X2 ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6172 X1 X0 X2
       have i₂ := eq1047112 X2 X1 (M.op X0 X0)
       grind)
    | exact superpose eq1047112 eq6172
    | (have j1 := eq1047112 X2 X1 x
       grind)
    | exact resolve eq6172 eq1047112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047112
  have eq1100151 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X3 X0) X4) = (k (M.op X1 (M.op X1 (M.op (M.op X2 X2) X3))) X4) ∨ (k X0 X3) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq115112 X1 (M.op (M.op X2 X2) X3) X4 X3
       have i₂ := eq1061441 X2 X3 X0
       grind)
    | (have i₁ := eq115112 X0 X1 X2 X3
       have i₂ := eq1061441 X0 X1 (M.op X3 X1)
       grind)
    | exact superpose eq1061441 eq115112
    | (have j1 := eq1061441 X0 X3 X0
       grind)
    | exact resolve eq115112 eq1061441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115112 eq1061441
  have eq1101469 : ∀ X0 X3 X4 : G, (k X3 X4) = (k (M.op X3 X0) X4) ∨ (k X0 X3) = (M.op X3 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq1100151 X0 x x X3 X4
       have i₂ := eq9 X3 x x
       grind)
    | exact superpose eq9 eq1100151
    | (have j0 := eq1100151 X0 x x X3 X4
       grind)
    | exact resolve eq1100151 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100151
  have eq1182904 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24081 X1 X0
       have i₂ := eq1101469 X0 X0 X0
       grind)
    | exact superpose eq1101469 eq24081
    | (have j1 := eq1101469 X0 X0 x
       grind)
    | exact resolve eq24081 eq1101469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101469
  have eq1223302 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1182904 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182904
  have eq1223316 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1223302 X0 x
       have j1 := eq1059593 X0 x X0
       grind)
    | (have r₁ := eq1223302 x x
       have r₂ := eq1059593 x x x
       grind)
    | exact resolve eq1223302 eq1059593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059593 eq1223302
  have eq1239015 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1223316 (σ X0)
       grind)
    | exact superpose eq1223316 eq15
    | exact resolve eq15 eq1223316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239030 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq1223316 (τ X0)
       grind)
    | exact superpose eq1223316 eq35
    | exact resolve eq35 eq1223316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239082 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1239030 X0
       have i₂ := eq1223316 X0
       grind)
    | exact superpose eq1223316 eq1239030
    | exact resolve eq1239030 eq1223316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239030
  have eq1239094 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1239015 X0
       have i₂ := eq1223316 X0
       grind)
    | exact superpose eq1223316 eq1239015
    | exact resolve eq1239015 eq1223316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223316 eq1239015
  have eq1250765 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (τ (M.op X0 X0)) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6172 X1 (τ X0) X2
       have i₂ := eq1239082 X0
       grind)
    | exact superpose eq1239082 eq6172
    | exact resolve eq6172 eq1239082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1250802 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24081 X1 (τ X0)
       have i₂ := eq1239082 X0
       grind)
    | exact superpose eq1239082 eq24081
    | exact resolve eq24081 eq1239082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1251075 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (M.op X1 X1) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6172 (τ X0) X1 (τ X0)
       have i₂ := eq1239082 X0
       grind)
    | exact superpose eq1239082 eq6172
    | exact resolve eq6172 eq1239082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239082
  have eq1251224 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1250802 X0 X1
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq1250802
    | exact resolve eq1250802 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1250802
  have eq1251334 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (τ X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq1251224
  have eq1261814 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24081 X1 (σ X0)
       have i₂ := eq1239094 X0
       grind)
    | exact superpose eq1239094 eq24081
    | exact resolve eq24081 eq1239094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24081
  have eq1262087 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X1 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6172 (σ X0) X1 (σ X0)
       have i₂ := eq1239094 X0
       grind)
    | exact superpose eq1239094 eq6172
    | exact resolve eq6172 eq1239094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6172
  have eq1262238 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1261814 X0 X1
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1261814
    | exact resolve eq1261814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261814
  have eq1262363 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    grind
  clear eq1262238
  have eq1300208 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1250765 (M.op (σ x) (σ x)) X0 X1
       have i₂ := eq155150 (σ x)
       grind)
    | exact superpose eq155150 eq1250765
    | exact resolve eq1250765 eq155150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250765
  have eq1384811 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 X1) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq889 x x (M.op x x) X1 (M.op (M.op x x) (M.op x x)) (τ X0)
       have i₂ := eq1251334 X0 (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x)))
       grind)
    | exact superpose eq1251334 eq889
    | exact resolve eq889 eq1251334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251334
  have eq1404444 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq889 x x (M.op x x) X1 (M.op (M.op x x) (M.op x x)) (σ X0)
       have i₂ := eq1262363 X0 (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) (M.op x x)))
       grind)
    | exact superpose eq1262363 eq889
    | exact resolve eq889 eq1262363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq1262363
  have eq1601709 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op X3 X3)) = (M.op (M.op X4 X4) (τ (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X2 X2) (M.op X3 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1384811 (M.op X3 X3) X4
       have i₂ := eq763 X2 (M.op X3 X3) X3 X3 X0 X1
       grind)
    | (have i₁ := eq1384811 (M.op (M.op X4 X4) (M.op X4 X4)) X1
       have i₂ := eq763 (M.op X4 X4) (M.op (M.op X4 X4) (M.op X4 X4)) X2 X3 X4 X4
       grind)
    | exact superpose eq763 eq1384811
    | exact resolve eq1384811 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq1384811
  have eq1653656 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 X2) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1404444 X1 X2
       have i₂ := eq25698 X1 X1 X0
       grind)
    | (have i₁ := eq1404444 X1 X2
       have i₂ := eq25698 X0 X1 X1
       grind)
    | exact superpose eq25698 eq1404444
    | exact resolve eq1404444 eq25698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25698 eq1404444
  have eq1830101 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op X1 X1) (τ (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ x))) (M.op (M.op X0 X0) (M.op (σ x) (σ x))))))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1251075 (M.op (M.op X0 X0) (M.op (σ x) (σ x))) X1
       have i₂ := eq155150 X0
       grind)
    | exact superpose eq155150 eq1251075
    | exact resolve eq1251075 eq155150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155150 eq1251075
  have eq1831858 : y = (M.op y (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1830101 x x
       have i₂ := eq1601709 x (σ x) x (σ x) x
       grind)
    | exact superpose eq1601709 eq1830101
    | exact resolve eq1830101 eq1601709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601709 eq1830101
  have eq1832022 : y = (M.op y (τ (σ (M.op x x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1831858
       have i₂ := eq1239094 x
       grind)
    | exact superpose eq1239094 eq1831858
    | exact resolve eq1831858 eq1239094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239094 eq1831858
  have eq1832069 : y = (M.op y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1832022
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1832022
    | exact resolve eq1832022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1832022
  have eq1908250 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1300208 x x
       have i₂ := eq1832069
       grind)
    | exact superpose eq1832069 eq1300208
    | exact resolve eq1300208 eq1832069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300208 eq1832069
  have eq1909893 : x = (M.op x y) := by grind
  clear eq1908250
  have eq1914618 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq1653656 x y X0
       have i₂ := eq1909893
       grind)
    | exact superpose eq1909893 eq1653656
    | exact resolve eq1653656 eq1909893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653656
  have eq3782382 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1262087 x x
       have i₂ := eq1914618 x
       grind)
    | exact superpose eq1914618 eq1262087
    | exact resolve eq1262087 eq1914618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262087 eq1914618
  have eq3835453 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3782382
       grind)
    | exact superpose eq3782382 eq16
    | exact resolve eq16 eq3782382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782382
  have eq3835926 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3835453
       have i₂ := eq1909893
       grind)
    | exact superpose eq1909893 eq3835453
    | exact resolve eq3835453 eq1909893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909893 eq3835453
  have eq3835927 : False := by grind
  exact eq3835927

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pyx_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq29 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq739 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq53 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq53 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1020 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq739 X1 X2 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq739
    | exact resolve eq739 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq3974 : ∀ X0 X1 X2 : G, (M.op (σ (σ (M.op X0 X0))) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1020 (σ X0) X1 X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq1020
    | exact resolve eq1020 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq36577 : ∀ X0 : G, y = (M.op (σ (M.op X0 X0)) (M.op y (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1020 X0 y y
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq1020
    | exact resolve eq1020 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq36584 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq36577 x
       have i₂ := eq1020 x y x
       grind)
    | exact superpose eq1020 eq36577
    | exact resolve eq36577 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq36577
  have eq36585 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq36584
  have eq36610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq36585 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq36585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36585
  have eq36611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq36610
    | exact resolve eq36610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36610
  have eq36622 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq36611
       have r₂ := eq28
       grind)
    | exact resolve eq36611 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36611
  have eq36763 : ∀ X0 : G, (σ y) = (M.op (σ (σ (M.op X0 X0))) (M.op (σ y) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq36622 eq3974
    | exact resolve eq3974 eq36622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36622
  have eq36764 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq36763 x
       have i₂ := eq3974 x sF3 sF2
       grind)
    | exact superpose eq3974 eq36763
    | exact resolve eq36763 eq3974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974 eq36763
  have eq36765 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq36764
  have eq36779 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq36765 eq30
    | exact resolve eq30 eq36765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36765
  have eq36926 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq36779
    | exact resolve eq36779 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq36779
  have eq36927 : x = y := by grind
  clear eq36926
  have eq37199 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq36927
       grind)
    | exact superpose eq36927 eq19
    | exact resolve eq19 eq36927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq37200 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq36927
       grind)
    | exact superpose eq36927 eq25
    | exact resolve eq25 eq36927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq36927
  have eq37348 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37200
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37200
    | exact resolve eq37200 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37200
  have eq37367 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37348 eq27
    | exact resolve eq27 eq37348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37348
  have eq38395 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37367 eq66
    | exact resolve eq66 eq37367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq37367
  have eq38586 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38395
       have i₂ := eq37199
       grind)
    | exact superpose eq37199 eq38395
    | exact resolve eq38395 eq37199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37199 eq38395
  have eq38599 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38586 eq15
    | exact resolve eq15 eq38586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38586
  have eq38679 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq38599
    | exact resolve eq38599 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq38599
  have eq38700 : False := by grind
  exact eq38700

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq30
    | (have j0 := eq30 X0 X1
       grind)
    | exact resolve eq30 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq147 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq24 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq24 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq249 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq44
    | (have j0 := eq44 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq774 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq147 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq147
    | exact resolve eq147 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28440 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq16
    | (have j1 := eq249 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq249 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq249 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq249 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq28558 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq28440
  have eq104181 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ (M.op x x)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq147 (σ x) (σ y) X0
       have i₂ := eq28558
       grind)
    | exact superpose eq28558 eq147
    | exact resolve eq147 eq28558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28558
  have eq104318 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq104181 x
       have i₂ := eq774 x x
       grind)
    | exact superpose eq774 eq104181
    | exact resolve eq104181 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq104181
  have eq104319 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq104318
  have eq106103 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq147 x y X0
       have i₂ := eq104319
       grind)
    | exact superpose eq104319 eq147
    | exact resolve eq147 eq104319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104319
  have eq106225 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq106103 x
       have i₂ := eq147 x x x
       grind)
    | exact superpose eq147 eq106103
    | exact resolve eq106103 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq106103
  have eq106226 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq106225
  have eq111480 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq106226
       grind)
    | exact superpose eq106226 eq10
    | exact resolve eq10 eq106226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106226
  have eq111587 : x = y ∨ x = y := by
    first
    | (have i₁ := eq111480
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq111480
    | exact resolve eq111480 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111480
  have eq111588 : x = y := by grind
  clear eq111587
  have eq122042 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111588
       grind)
    | exact superpose eq111588 eq16
    | exact resolve eq16 eq111588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111588
  have eq122043 : False := by grind
  exact eq122043

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pyx_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (M.op x y) = (M.op x y) := by grind
  have eq19 : (M.op x y) = (M.op x y) := by grind
  clear eq18
  have eq20 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq20
  have eq22 : (σ x) = (σ x) := by grind
  have eq23 : (σ x) = (σ x) := by grind
  clear eq22
  have eq24 : (σ y) = (σ y) := by grind
  have eq25 : (σ y) = (σ y) := by grind
  clear eq24
  have eq26 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq26
  have eq28 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq34
  have eq45 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq9 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq9 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq97
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq282 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) = (σ (M.op (M.op X0 X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq35 (M.op X1 X1)
       have i₂ := eq64 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq64 eq35
    | exact resolve eq35 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq64 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X0 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X1 X1) X2
       have i₂ := eq64 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq282
    | exact resolve eq282 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq293 : y ≠ (M.op x y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq75 eq294
    | exact resolve eq294 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq325 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq75
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq327 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq325
    | exact resolve eq325 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq329 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq327
    | exact resolve eq327 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq329
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq329
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq331
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq331
    | exact resolve eq331 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq341
    | exact resolve eq341 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq343 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq342
       have r₂ := eq28
       grind)
    | exact resolve eq342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq344 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq343
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq343
    | exact resolve eq343 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq345 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq344 eq295
    | (have r₁ := eq295
       have r₂ := eq344
       grind)
    | exact resolve eq295 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq344
  have eq347 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq345
  have eq348 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq347
  have eq349 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq348
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq348
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq348 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq348
       grind)
    | exact superpose eq348 eq10
    | exact resolve eq10 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq363 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq349
  have eq372 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq46 eq352
    | exact resolve eq352 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq373 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq363
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq363
    | exact resolve eq363 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq374 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq372
       have r₂ := eq293
       grind)
    | exact resolve eq372 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq372
  have eq375 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq373
    | exact resolve eq373 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq376 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq375
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq375
    | exact resolve eq375 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq377 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq376
  have eq380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq329
       have i₂ := eq374
       grind)
    | exact superpose eq374 eq329
    | exact resolve eq329 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq374
  have eq384 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq380
  have eq388 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq384
    | exact resolve eq384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq396 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq377 eq47
    | exact resolve eq47 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq377
  have eq403 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq46 eq396
    | exact resolve eq396 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq404 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq403
  have eq412 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq404 eq46
    | exact resolve eq46 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq419 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq45 eq412
    | exact resolve eq412 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq424 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq419 eq21
    | exact resolve eq21 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq424
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq424
    | exact resolve eq424 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq430 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq428 eq27
    | exact resolve eq27 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq63 X1 X4 x x
       have i₂ := eq63 X1 X0 x x
       grind)
    | (have i₁ := eq63 X0 X1 x x
       have i₂ := eq63 X0 (M.op x x) x x
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq63 (M.op X5 X2) X5 X3 X4
       have i₂ := eq63 X2 X5 X0 X1
       grind)
    | (have i₁ := eq63 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
       have i₂ := eq63 X0 X1 X2 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq63 X1 X0 x X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq63 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X2 X2) x
       have i₂ := eq63 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq63 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X1 X1) (M.op X1 X1))) (σ (M.op (M.op X1 X1) (M.op X1 X1)))) = (σ (M.op X0 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq63 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq63 eq35
    | exact resolve eq35 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq63 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq63 eq64
    | exact resolve eq64 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq64
  have eq520 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (M.op X1 X1)))) = (M.op (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq35 (M.op X1 X1)
       grind)
    | exact superpose eq35 eq507
    | exact resolve eq507 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq526 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (M.op X1 X1)))) = (M.op (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq520
    | exact resolve eq520 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq605 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq388 eq28
    | exact resolve eq28 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq623 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq428 eq605
    | (have r₁ := eq605
       have r₂ := eq428
       grind)
    | exact resolve eq605 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq624 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq623
  have eq625 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq624
  have eq849 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X3) X0)))) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq486 X1 (M.op X2 (M.op (M.op X3 X3) X0)) X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq486
    | exact resolve eq486 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq856 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq486 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq486
    | (have j0 := eq486 x y X0
       grind)
    | exact resolve eq486 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq859 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq486
    | (have j0 := eq486 X0 (σ y) (σ x)
       grind)
    | exact resolve eq486 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq430 eq486
    | exact resolve eq486 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq1337 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq504 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq504
    | (have j0 := eq504 x y X0
       grind)
    | exact resolve eq504 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1341 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq504
    | (have j0 := eq504 (σ x) (σ y) X0
       grind)
    | exact resolve eq504 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15444 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (σ (M.op x y))) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq860 eq285
    | exact resolve eq285 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15523 : ∀ X0 X2 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (M.op X2 X2) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq1341 eq15444
    | exact resolve eq15444 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq15444
  have eq26346 : ∀ X0 X1 X2 X3 : G, (M.op X3 (σ (M.op x y))) = (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X0 X0) (σ y))))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq15523 eq491
    | exact resolve eq491 eq15523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15523
  have eq26392 : ∀ X3 : G, (M.op X3 (σ (M.op x y))) = (M.op X3 (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X3
    first
    | (have i₁ := eq26346 x x x X3
       have i₂ := eq491 sF3 x x X3 x
       grind)
    | exact superpose eq491 eq26346
    | exact resolve eq26346 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq26346
  have eq26422 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op (σ y) (σ (M.op x y))) X1))) = X1 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26392 eq9
    | exact resolve eq9 eq26392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26454 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ (M.op x y))) (M.op X0 (M.op X0 X1))) = X1 ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26392 eq504
    | exact resolve eq504 eq26392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26392
  have eq33392 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) = (M.op X7 (M.op X7 (M.op X2 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X3)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq503 X2 (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3)) X7 X4
       have i₂ := eq492 X5 X6 X3 X0 X1 X2
       grind)
    | (have i₁ := eq503 (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2)) X2 X4
       have i₂ := eq492 X0 X1 X2 X3 X4 X5
       grind)
    | exact superpose eq492 eq503
    | exact resolve eq503 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq503
  have eq33468 : ∀ X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) = (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) := by
    intro X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq33392 x X1 X2 X3 X4 X5 X6 x
       have i₂ := eq849 (M.op (M.op X1 X1) (M.op X2 X3)) x X2 x
       grind)
    | exact superpose eq849 eq33392
    | exact resolve eq33392 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq33392
  have eq33697 : ∀ X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq33468 X1 X2 X3 x x x
       have i₂ := eq285 x x x X3
       grind)
    | exact superpose eq285 eq33468
    | exact resolve eq33468 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285 eq33468
  have eq51373 : y = (M.op (M.op (σ y) (σ (M.op x y))) (M.op x (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26454 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26454
    | (have j0 := eq26454 x y
       grind)
    | exact resolve eq26454 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26454
  have eq51547 : y = (M.op (M.op (σ y) (σ (M.op x y))) (M.op x y)) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq419 eq51373
    | exact resolve eq51373 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51373
  have eq51566 : y = (M.op (M.op (σ y) (σ (M.op x y))) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq51547
  have eq51576 : y = (M.op (M.op (σ y) (σ (M.op x y))) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51566
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51566
    | exact resolve eq51566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51566
  have eq51581 : y = (M.op (M.op (σ y) (σ (M.op x y))) y) ∨ x = y ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq419 eq51576
    | exact resolve eq51576 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq51576
  have eq51604 : y = (M.op (M.op (σ y) (σ (M.op x y))) y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq51581
  have eq52130 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq51604 eq26422
    | exact resolve eq26422 eq51604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26422 eq51604
  have eq52146 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq52130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52130
  have eq64388 : (σ (M.op y y)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq526 y y
       have i₂ := eq52146 y
       grind)
    | exact superpose eq52146 eq526
    | exact resolve eq526 eq52146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq52146
  have eq64554 : (σ (M.op y y)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64388
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64388
    | exact resolve eq64388 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64388
  have eq64615 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64554
       have i₂ := eq35 y
       grind)
    | exact superpose eq35 eq64554
    | exact resolve eq64554 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64554
  have eq64654 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64615
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq64615
    | exact resolve eq64615 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64615
  have eq73183 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op y (M.op x (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq509 y y X0 X1
       have i₂ := eq856 y
       grind)
    | exact superpose eq856 eq509
    | exact resolve eq509 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq73514 : (M.op (σ y) (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64654
       have i₂ := eq73183 (M.op sF3 sF3) (M.op (M.op sF3 sF3) (M.op sF3 sF3))
       grind)
    | exact superpose eq73183 eq64654
    | exact resolve eq64654 eq73183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64654
  have eq73519 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X1 X1))) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq73183 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact superpose eq73183 eq286
    | exact resolve eq286 eq73183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq74310 : (M.op (σ y) (σ y)) = (M.op (M.op y (M.op x (M.op x y))) (M.op (M.op y (M.op x (M.op x y))) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73514
       have i₂ := eq73183 sF3 (M.op sF3 sF3)
       grind)
    | exact superpose eq73183 eq73514
    | exact resolve eq73514 eq73183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73183 eq73514
  have eq76390 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 (σ y)))) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq859 eq486
    | exact resolve eq486 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq76536 : (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76390 eq74310
    | exact resolve eq74310 eq76390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74310 eq76390
  have eq76577 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76536 eq504
    | exact resolve eq504 eq76536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76536
  have eq76596 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76577 x
       have i₂ := eq504 sF3 sF3 x
       grind)
    | exact superpose eq504 eq76577
    | exact resolve eq76577 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76577
  have eq76616 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76596 eq859
    | exact resolve eq859 eq76596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859 eq76596
  have eq76658 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq428 eq76616
    | exact resolve eq76616 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428 eq76616
  have eq76822 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq76658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76658
  have eq77726 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq76822 eq860
    | exact resolve eq860 eq76822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq76822
  have eq77827 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq77726
  have eq77867 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq625 eq77827
    | exact resolve eq77827 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq77827
  have eq77907 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq77867
  have eq79474 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq33697 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq33697
    | (have j0 := eq33697 X0 x y
       grind)
    | exact resolve eq33697 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82837 : (τ (σ (M.op x y))) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq77907 eq161
    | exact resolve eq161 eq77907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq77907
  have eq82953 : (τ (σ (M.op x y))) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq46 eq82837
    | exact resolve eq82837 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82837
  have eq82955 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq45 eq82953
    | exact resolve eq82953 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82953
  have eq85309 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 X0) (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq33697 X0 x x
       have i₂ := eq82955
       grind)
    | exact superpose eq82955 eq33697
    | exact resolve eq33697 eq82955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82955
  have eq85339 : x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq79474 eq85309
    | exact resolve eq85309 eq79474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79474 eq85309
  have eq85340 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq85339
  have eq85352 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq85340 eq46
    | exact resolve eq46 eq85340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq85340
  have eq85579 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq45 eq85352
    | exact resolve eq85352 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq85352
  have eq85580 : x = (M.op x y) ∨ x = y := by grind
  clear eq85579
  have eq85585 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq85580 eq21
    | exact resolve eq21 eq85580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85601 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq85580 eq856
    | exact resolve eq856 eq85580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq85607 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq85580 eq1337
    | exact resolve eq1337 eq85580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85580
  have eq85829 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq85585
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq85585
    | exact resolve eq85585 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85585
  have eq87972 : ∀ X0 X1 : G, (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) = (σ (M.op (M.op X1 X1) (M.op X0 (M.op X0 y)))) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq73519 X1 x
       have i₂ := eq85601 X0
       grind)
    | exact superpose eq85601 eq73519
    | exact resolve eq73519 eq85601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73519 eq85601
  have eq88182 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq87972 x x
       have i₂ := eq504 x y x
       grind)
    | exact superpose eq504 eq87972
    | exact resolve eq87972 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq87972
  have eq88218 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq88182
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq88182
    | exact resolve eq88182 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88182
  have eq88222 : (σ y) = (M.op (M.op y (M.op x (M.op x y))) (M.op (σ x) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq88218
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq88218
    | exact resolve eq88218 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88218
  have eq88519 : y = (M.op y (M.op x (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1337 (M.op x x)
       have i₂ := eq85607 x
       grind)
    | exact superpose eq85607 eq1337
    | exact resolve eq1337 eq85607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq88532 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq33697 (M.op x x) X0 X1
       have i₂ := eq85607 x
       grind)
    | exact superpose eq85607 eq33697
    | exact resolve eq33697 eq85607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33697 eq85607
  have eq168296 : (σ y) = (M.op y (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq88519 eq88222
    | exact resolve eq88222 eq88519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88222 eq88519
  have eq168362 : (σ y) = (M.op y (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq168296
  have eq168396 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq168362 eq88532
    | exact resolve eq88532 eq168362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88532 eq168362
  have eq168437 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq168396
  have eq168450 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq168437
    | exact resolve eq168437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168437
  have eq168458 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq168450 eq28
    | exact resolve eq28 eq168450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168450
  have eq168608 : x = y := by
    first
    | (have r₁ := eq168458
       have r₂ := eq85829
       grind)
    | exact resolve eq168458 eq85829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85829 eq168458
  have eq168609 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq168608
       grind)
    | exact superpose eq168608 eq19
    | exact resolve eq19 eq168608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq168610 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq168608
       grind)
    | exact superpose eq168608 eq25
    | exact resolve eq25 eq168608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq168608
  have eq171246 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq168610
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq168610
    | exact resolve eq168610 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168610
  have eq171847 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq171246 eq27
    | exact resolve eq27 eq171246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq171246
  have eq175197 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq168609
       grind)
    | exact superpose eq168609 eq35
    | exact resolve eq35 eq168609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq168609
  have eq177725 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq175197
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq175197
    | exact resolve eq175197 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq175197
  have eq180121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq171847 eq177725
    | exact resolve eq177725 eq171847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171847 eq177725
  have eq182172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq180121
    | exact resolve eq180121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq180121
  have eq183611 : False := by grind
  exact eq183611

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation826 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq95 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq95 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq190 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq191 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq199 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq200 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq374 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq200
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq399 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq374
    | (have j0 := eq374 X0 X1
       grind)
    | exact resolve eq374 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq374
  have eq404 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq399
    | exact resolve eq399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq543 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq381
       have i₂ := eq404 x y
       grind)
    | exact superpose eq404 eq381
    | (have j1 := eq404 (σ x) (σ y)
       grind)
    | (have r₁ := eq381
       have r₂ := eq404 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq381
       have r₂ := eq404 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq381 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq404
  have eq546 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq543
  have eq548 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq546
       grind)
    | exact superpose eq546 eq10
    | exact resolve eq10 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq583 : x = y ∨ x = y := by
    first
    | (have i₁ := eq548
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq548
    | exact resolve eq548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq584 : x = y := by grind
  clear eq583
  have eq630 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq584
       grind)
    | exact superpose eq584 eq16
    | exact resolve eq16 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq631 : False := by grind
  exact eq631
