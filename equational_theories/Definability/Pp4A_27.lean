import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq320 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq326 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq320 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq325 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq325 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq325 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq338 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq327 (σ X0)
       grind)
    | exact superpose eq327 eq15
    | exact resolve eq15 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq338
    | exact resolve eq338 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq338
  have eq409 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq67
    | exact resolve eq67 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq614 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq326 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq615 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq614 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq627 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq615 X0 (τ X1)
       grind)
    | exact superpose eq615 eq18
    | (have j1 := eq615 X0 (τ X1)
       grind)
    | exact resolve eq18 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq630 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq615 (σ X0) (σ X1)
       grind)
    | exact superpose eq615 eq15
    | (have j1 := eq615 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq1194 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq627 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq627
    | exact resolve eq627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq1277 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1194 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1194
    | (have j0 := eq1194 X0 X1
       grind)
    | exact resolve eq1194 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq2673 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq630 x y
       grind)
    | exact superpose eq630 eq16
    | (have j1 := eq630 x y
       grind)
    | exact resolve eq16 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2728 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq630 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq2974 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2673
       have i₂ := eq1277 y x
       grind)
    | exact superpose eq1277 eq2673
    | (have j1 := eq1277 (σ y) (σ x)
       grind)
    | (have r₁ := eq2673
       have r₂ := eq1277 y x
       grind)
    | exact resolve eq2673 eq1277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2673
  have eq2975 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2974
  have eq2980 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2975
       grind)
    | exact superpose eq2975 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2975
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2975
       grind)
    | exact resolve eq13 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq2989 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2980
  have eq20329 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2728 x y
       have i₂ := eq2989
       grind)
    | exact superpose eq2989 eq2728
    | (have j0 := eq2728 x y
       grind)
    | exact resolve eq2728 eq2989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728 eq2989
  have eq20337 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq20329
  have eq20338 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq20337
  have eq20470 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20338
       grind)
    | exact superpose eq20338 eq16
    | exact resolve eq16 eq20338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20481 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq20338
       grind)
    | exact superpose eq20338 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20338
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq20338
       grind)
    | exact resolve eq13 eq20338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20338
  have eq20497 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq20481
  have eq20503 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20497
       have i₂ := eq357 y
       grind)
    | exact superpose eq357 eq20497
    | exact resolve eq20497 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20497
  have eq20510 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20503
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20503
    | exact resolve eq20503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20503
  have eq35938 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1277 y x
       have i₂ := eq20510
       grind)
    | exact superpose eq20510 eq1277
    | (have j0 := eq1277 y x
       grind)
    | exact resolve eq1277 eq20510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq20510
  have eq36072 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq35938
       have r₂ := eq20470
       grind)
    | exact resolve eq35938 eq20470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35938
  have eq36140 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20470
       have i₂ := eq36072
       grind)
    | exact superpose eq36072 eq20470
    | exact resolve eq20470 eq36072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20470 eq36072
  have eq36172 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq36140
  have eq36173 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq36172
  have eq36195 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq409 y X0
       have i₂ := eq36173
       grind)
    | exact superpose eq36173 eq409
    | (have j0 := eq409 y X0
       grind)
    | (have r₁ := eq409 y x
       have r₂ := eq36173
       grind)
    | exact resolve eq409 eq36173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36196 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq36173
       grind)
    | exact superpose eq36173 eq410
    | exact resolve eq410 eq36173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq36173
  have eq36254 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq36195 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36195
  have eq36264 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq36196
       have i₂ := eq357 y
       grind)
    | exact superpose eq357 eq36196
    | exact resolve eq36196 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq36196
  have eq36265 : (σ y) = (σ (M.op y y)) := by grind
  clear eq36264
  have eq36266 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq36254 X0
       have j1 := eq409 y X0
       grind)
    | (have r₁ := eq36254 X0
       have r₂ := eq409 y x
       grind)
    | exact resolve eq36254 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq36254
  have eq36297 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq36265
       grind)
    | exact superpose eq36265 eq10
    | exact resolve eq10 eq36265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36265
  have eq36423 : y = (M.op y y) := by
    first
    | (have i₁ := eq36297
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq36297
    | exact resolve eq36297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36297
  have eq36446 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq36423
       grind)
    | exact superpose eq36423 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq36423
       grind)
    | exact resolve eq12 eq36423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36423
  have eq36518 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq36446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36446
  have eq36763 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq36266 (σ X0)
       grind)
    | exact superpose eq36266 eq15
    | exact resolve eq15 eq36266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36266
  have eq36803 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq36763 X0
       have i₂ := eq36518 X0
       grind)
    | exact superpose eq36518 eq36763
    | exact resolve eq36763 eq36518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36518 eq36763
  have eq37092 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36803 x
       grind)
    | exact superpose eq36803 eq16
    | (have r₁ := eq16
       have r₂ := eq36803 x
       grind)
    | exact resolve eq16 eq36803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36803
  have eq37209 : False := by grind
  exact eq37209

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq18 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq20 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op X0 X0)
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq10
    | exact resolve eq10 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq35
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 (σ X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq41
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq41 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq35
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq35 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (k X0 (σ X1)) (σ X2)
       have i₂ := eq34 X0 X1 X2
       grind)
    | exact superpose eq34 eq14
    | (have j0 := eq14 (k X0 (σ X1)) (σ X2)
       grind)
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq242 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ x)
       have i₂ := eq68 x x
       grind)
    | exact superpose eq68 eq25
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq25 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq246 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq248 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq243 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq249 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq252 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq249 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq249 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq333 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq246 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq246
    | (have j0 := eq246 (τ X0)
       grind)
    | exact resolve eq246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq335 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq333 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq333
    | (have j0 := eq333 X0
       grind)
    | exact resolve eq333 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq338 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq335 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq335
    | (have j0 := eq335 X0
       grind)
    | exact resolve eq335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq347 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X0))) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (σ X0) X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq252
    | (have j0 := eq252 (σ X0) X1
       grind)
    | exact resolve eq252 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq252 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq252
    | (have j0 := eq252 (τ X0) X1
       grind)
    | exact resolve eq252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq350 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq350
    | (have j0 := eq350 X0 X1
       grind)
    | exact resolve eq350 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq355 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq361 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 (τ X0) X1
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq355
    | (have j0 := eq355 (τ X0) X1
       grind)
    | exact resolve eq355 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1581 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq248 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq248
    | (have j0 := eq248 (τ X0)
       grind)
    | exact resolve eq248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq1625 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1581 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1581
    | (have j0 := eq1581 X0
       grind)
    | exact resolve eq1581 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581
  have eq1638 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1625 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1625
    | (have j0 := eq1625 X0
       grind)
    | exact resolve eq1625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq4558 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq69 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq4559 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq4558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq4562 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4559 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4559
    | (have j0 := eq4559 X0
       grind)
    | exact resolve eq4559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4565 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4562 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4562
    | exact resolve eq4562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4562
  have eq4620 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4565 X0
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq4565
    | (have j0 := eq4565 X0
       grind)
    | exact resolve eq4565 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4697 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4620 X0
       grind)
    | exact superpose eq4620 eq11
    | (have j1 := eq4620 X0
       grind)
    | exact resolve eq11 eq4620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4620
  have eq4805 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4697 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4697
    | (have j0 := eq4697 X0
       grind)
    | exact resolve eq4697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4697
  have eq4819 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4805 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4805 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4805 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805
  have eq4824 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X0 X1
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq252
    | (have j0 := eq252 X0 X1
       grind)
    | exact resolve eq252 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq4828 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq347
    | (have j0 := eq347 X0 X1
       grind)
    | exact resolve eq347 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq4830 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 X0 X1
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq361
    | (have j0 := eq361 X0 X1
       grind)
    | exact resolve eq361 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq4862 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4819 (σ X0)
       grind)
    | exact superpose eq4819 eq15
    | exact resolve eq15 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4869 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0 X0
       have i₂ := eq4819 (τ X0)
       grind)
    | exact superpose eq4819 eq47
    | exact resolve eq47 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4918 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4869 X0
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq4869
    | exact resolve eq4869 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4869
  have eq4925 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4862 X0
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq4862
    | exact resolve eq4862 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4862
  have eq5314 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (τ X0)
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq25
    | exact resolve eq25 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq5326 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (τ X0) (τ X0)
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq20
    | exact resolve eq20 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5420 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) (σ X0)
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq20
    | exact resolve eq20 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13522 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5314 (σ X1)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq5314
    | (have j1 := eq72 X1 X0
       grind)
    | exact resolve eq5314 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq5314
  have eq13617 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13522 X0 X1
       have i₂ := eq4918 (σ X0)
       grind)
    | exact superpose eq4918 eq13522
    | (have j0 := eq13522 X0 X1
       grind)
    | exact resolve eq13522 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13522
  have eq13641 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13617 X0 X1
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq13617
    | (have j0 := eq13617 X0 X1
       grind)
    | exact resolve eq13617 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13617
  have eq13652 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13641 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq13641
    | (have j0 := eq13641 X0 X1
       grind)
    | exact resolve eq13641 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13641
  have eq13657 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13652 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq13652
    | (have j0 := eq13652 X0 X1
       grind)
    | exact resolve eq13652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13652
  have eq33508 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1638 (σ X0)
       have i₂ := eq216 (σ X0) X0 X0
       grind)
    | exact superpose eq216 eq1638
    | (have j0 := eq1638 (σ X0)
       have j1 := eq216 (σ X0) X0 X0
       grind)
    | exact resolve eq1638 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq1638
  have eq33561 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq33508 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33508
  have eq33614 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have j0 := eq33561 X0
       have j1 := eq338 (σ X0)
       grind)
    | (have r₁ := eq33561 X0
       have r₂ := eq338 (σ X0)
       grind)
    | exact resolve eq33561 eq338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338 eq33561
  have eq33707 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq33614 X0
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq33614
    | (have j0 := eq33614 X0
       grind)
    | exact resolve eq33614 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33614
  have eq33726 : ∀ X0 : G, (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33707 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33707
    | (have j0 := eq33707 X0
       grind)
    | exact resolve eq33707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33707
  have eq33737 : ∀ X0 : G, (M.op (k (σ X0) (σ X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33726 X0
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq33726
    | (have j0 := eq33726 X0
       grind)
    | exact resolve eq33726 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33726
  have eq33745 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33737 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq33737
    | (have j0 := eq33737 X0
       grind)
    | exact resolve eq33737 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33737
  have eq33751 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33745 X0
       have i₂ := eq4819 X0
       grind)
    | exact superpose eq4819 eq33745
    | (have j0 := eq33745 X0
       grind)
    | exact resolve eq33745 eq4819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819 eq33745
  have eq33769 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (σ (k (M.op (τ X0) (τ X0)) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq33751 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq33751
    | exact resolve eq33751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33751
  have eq33914 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq33769 X0
       have i₂ := eq18 X0 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq18 eq33769
    | (have j0 := eq33769 X0
       grind)
    | exact resolve eq33769 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33769
  have eq33953 : ∀ X0 : G, (M.op (σ (τ (M.op X0 X0))) X0) = (k (σ (τ (M.op X0 X0))) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq33914 X0
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq33914
    | (have j0 := eq33914 X0
       grind)
    | exact resolve eq33914 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33914
  have eq33969 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq33953 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq33953
    | (have j0 := eq33953 X0
       grind)
    | exact resolve eq33953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33953
  have eq33980 : ∀ X0 : G, (σ (τ (M.op X0 X0))) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq33969 X0
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq33969
    | (have j0 := eq33969 X0
       grind)
    | exact resolve eq33969 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33969
  have eq33988 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq33980 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq33980
    | (have j0 := eq33980 X0
       grind)
    | exact resolve eq33980 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33980
  have eq33994 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq33988 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq33988 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq33988 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33988
  have eq34020 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq33994 (σ X0)
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq33994
    | exact resolve eq33994 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34022 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33994 (τ X0)
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq33994
    | exact resolve eq33994 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34145 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34022 X0
       have i₂ := eq47 X0 (M.op X0 X0)
       grind)
    | exact superpose eq47 eq34022
    | exact resolve eq34022 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34022
  have eq34147 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34020 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq34020
    | exact resolve eq34020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34020
  have eq34189 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34145 X0
       have i₂ := eq33994 X0
       grind)
    | exact superpose eq33994 eq34145
    | exact resolve eq34145 eq33994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34145
  have eq34191 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34147 X0
       have i₂ := eq33994 X0
       grind)
    | exact superpose eq33994 eq34147
    | exact resolve eq34147 eq33994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33994 eq34147
  have eq35820 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5420 X0
       have i₂ := eq34191 X0
       grind)
    | exact superpose eq34191 eq5420
    | exact resolve eq5420 eq34191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5420
  have eq35992 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (M.op (σ (M.op X0 X0)) (σ X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35820 (σ X0)
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq35820
    | exact resolve eq35820 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36161 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ (M.op (M.op X0 X0) X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq35992 X0
       have i₂ := eq34191 X0
       grind)
    | exact superpose eq34191 eq35992
    | exact resolve eq35992 eq34191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35992
  have eq81481 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq13657 X1 X0
       grind)
    | exact superpose eq13657 eq11
    | (have j1 := eq13657 X1 X0
       grind)
    | exact resolve eq11 eq13657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13657
  have eq81641 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81481 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq81481
    | (have j0 := eq81481 X0 X1
       grind)
    | exact resolve eq81481 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81481
  have eq83176 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81641 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81641
    | (have j0 := eq81641 X0 (τ X0)
       grind)
    | exact resolve eq81641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81641
  have eq83381 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83176 X0 X1
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq83176
    | (have j0 := eq83176 X0 X1
       grind)
    | exact resolve eq83176 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83176
  have eq83433 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5326 X0
       have i₂ := eq83381 X0 X1
       grind)
    | exact superpose eq83381 eq5326
    | (have j1 := eq83381 X0 X1
       grind)
    | exact resolve eq5326 eq83381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5326 eq83381
  have eq83720 : ∀ X0 X1 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83433 X0 X1
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq83433
    | (have j0 := eq83433 X0 X1
       grind)
    | exact resolve eq83433 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83433
  have eq83742 : ∀ X0 X1 : G, (τ X0) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83720 X0 X1
       have i₂ := eq34189 X0
       grind)
    | exact superpose eq34189 eq83720
    | (have j0 := eq83720 X0 X1
       grind)
    | exact resolve eq83720 eq34189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83720
  have eq85931 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (M.op X0 X0) X0)
       have i₂ := eq83742 X0 X1
       grind)
    | exact superpose eq83742 eq11
    | (have j1 := eq83742 X0 X1
       grind)
    | exact resolve eq11 eq83742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83742
  have eq86151 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq85931 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85931
    | (have j0 := eq85931 X0 X1
       grind)
    | exact resolve eq85931 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85931
  have eq86569 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35820 X0
       have i₂ := eq86151 X0 X1
       grind)
    | exact superpose eq86151 eq35820
    | (have j1 := eq86151 X0 X1
       grind)
    | exact resolve eq35820 eq86151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35820
  have eq86801 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86569 X0 X1
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq86569
    | (have j0 := eq86569 X0 X1
       grind)
    | exact resolve eq86569 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86569
  have eq86922 : ∀ X0 X1 X2 : G, (σ (σ X0)) ≠ (σ (σ X0)) ∨ (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4828 X0 X1
       have i₂ := eq86801 X0 X2
       grind)
    | exact superpose eq86801 eq4828
    | (have j0 := eq4828 X0 X1
       have j1 := eq86801 X0 X2
       grind)
    | exact resolve eq4828 eq86801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828 eq86801
  have eq87104 : ∀ X0 X1 X2 : G, (M.op X1 (σ (σ X0))) = (k X1 (σ (σ X0))) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq86922 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86922
  have eq211500 : ∀ X0 X1 X2 : G, (k X0 (τ (σ (σ X1)))) = (τ (M.op (σ X0) (σ (σ X1)))) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X0 (σ (σ X1))
       have i₂ := eq87104 X1 (σ X0) X2
       grind)
    | exact superpose eq87104 eq41
    | (have j1 := eq87104 X1 X1 X2
       grind)
    | exact resolve eq41 eq87104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq87104
  have eq211600 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (τ (M.op (σ X0) (σ (σ X1)))) ∨ (M.op X2 X1) = (k X2 X1) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq211500 X0 X1 X2
       have i₂ := eq10 (σ X1)
       grind)
    | exact superpose eq10 eq211500
    | (have j0 := eq211500 X0 X1 X2
       grind)
    | exact resolve eq211500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211500
  have eq296477 : ∀ X0 X1 : G, (τ (σ (σ X0))) = (k (σ (M.op (M.op X0 X0) X0)) (σ X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq211600 (σ (M.op (M.op X0 X0) X0)) X0 X1
       have i₂ := eq36161 X0
       grind)
    | exact superpose eq36161 eq211600
    | (have j0 := eq211600 X0 X0 X1
       grind)
    | exact resolve eq211600 eq36161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36161 eq211600
  have eq296980 : ∀ X0 X1 : G, (τ (σ (σ X0))) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq296477 X0 X1
       have i₂ := eq15 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq15 eq296477
    | (have j0 := eq296477 X0 X1
       grind)
    | exact resolve eq296477 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296477
  have eq297147 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq296980 X0 X1
       have i₂ := eq10 (σ X0)
       grind)
    | exact superpose eq10 eq296980
    | (have j0 := eq296980 X0 X1
       grind)
    | exact resolve eq296980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296980
  have eq298558 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op (M.op X0 X0) X0) X0)
       have i₂ := eq297147 X0 X1
       grind)
    | exact superpose eq297147 eq10
    | (have j1 := eq297147 X0 X1
       grind)
    | exact resolve eq10 eq297147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297147
  have eq298989 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq298558 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq298558
    | (have j0 := eq298558 X0 X1
       grind)
    | exact resolve eq298558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298558
  have eq299386 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq298989 X0 (M.op (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298989
  have eq299388 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq299386 X0
       grind)
    | (have r₁ := eq299386 X0
       have r₂ := eq20 X0 X0
       grind)
    | exact resolve eq299386 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299386
  have eq299466 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq299388 X0
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq299388
    | (have j0 := eq299388 X0
       grind)
    | exact resolve eq299388 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299388
  have eq300827 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (M.op (τ X0) (τ X0)) (τ X0))
       have i₂ := eq299466 (τ X0)
       grind)
    | exact superpose eq299466 eq18
    | (have j1 := eq299466 (τ X0)
       grind)
    | exact resolve eq18 eq299466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq299466
  have eq300972 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq300827 X0
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq300827
    | (have j0 := eq300827 X0
       grind)
    | exact resolve eq300827 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300827
  have eq301097 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ (M.op (M.op X0 X0) X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq300972 X0
       have i₂ := eq34189 X0
       grind)
    | exact superpose eq34189 eq300972
    | (have j0 := eq300972 X0
       grind)
    | exact resolve eq300972 eq34189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300972
  have eq301176 : ∀ X0 : G, (σ (τ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq301097 X0
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq301097
    | (have j0 := eq301097 X0
       grind)
    | exact resolve eq301097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301097
  have eq301250 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq301176 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq301176
    | (have j0 := eq301176 X0
       grind)
    | exact resolve eq301176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301176
  have eq301304 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))) ∨ (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq301250 X0
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq301250
    | (have j0 := eq301250 X0
       grind)
    | exact resolve eq301250 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301250
  have eq301348 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) X0))) ∨ (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq301304 X0
       have i₂ := eq34189 X0
       grind)
    | exact superpose eq34189 eq301304
    | (have j0 := eq301304 X0
       grind)
    | exact resolve eq301304 eq34189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301304
  have eq301474 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (M.op (σ (M.op X0 X0)) (σ X0)))) ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq301348 (σ X0)
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq301348
    | exact resolve eq301348 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301348
  have eq301779 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ (M.op (M.op X0 X0) X0)))) ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq301474 X0
       have i₂ := eq34191 X0
       grind)
    | exact superpose eq34191 eq301474
    | (have j0 := eq301474 X0
       grind)
    | exact resolve eq301474 eq34191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301474
  have eq301904 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq301779 X0
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq301779
    | (have j0 := eq301779 X0
       grind)
    | exact resolve eq301779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301779
  have eq301985 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = X0 ∨ (σ X0) = (k (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq301904 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq301904
    | (have j0 := eq301904 X0
       grind)
    | exact resolve eq301904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301904
  have eq302051 : ∀ X0 : G, (σ X0) = (k (σ (M.op (M.op X0 X0) X0)) (σ X0)) ∨ (M.op X0 (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq301985 X0
       have i₂ := eq34191 X0
       grind)
    | exact superpose eq34191 eq301985
    | (have j0 := eq301985 X0
       grind)
    | exact resolve eq301985 eq34191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301985
  have eq302108 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = X0 ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq302051 X0
       have i₂ := eq15 (M.op (M.op X0 X0) X0) X0
       grind)
    | exact superpose eq15 eq302051
    | (have j0 := eq302051 X0
       grind)
    | exact resolve eq302051 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302051
  have eq303371 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X0)) X0) = X0 ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq302108 X0
       grind)
    | exact superpose eq302108 eq20
    | (have j1 := eq302108 X0
       grind)
    | exact resolve eq20 eq302108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306500 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq303371 X0
       have i₂ := eq302108 X0
       grind)
    | exact superpose eq302108 eq303371
    | (have j0 := eq303371 X0
       have j1 := eq302108 X0
       grind)
    | exact resolve eq303371 eq302108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302108 eq303371
  have eq306779 : ∀ X0 : G, (σ X0) = (σ (k (M.op (M.op X0 X0) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq306500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306500
  have eq308249 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op (M.op X0 X0) X0) X0)
       have i₂ := eq306779 X0
       grind)
    | exact superpose eq306779 eq10
    | (have j1 := eq306779 X0
       grind)
    | exact resolve eq10 eq306779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306779
  have eq308700 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq308249 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq308249
    | (have j0 := eq308249 X0
       grind)
    | exact resolve eq308249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308249
  have eq308870 : ∀ X0 : G, (τ X0) = (k (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq308700 (τ X0)
       have i₂ := eq4918 X0
       grind)
    | exact superpose eq4918 eq308700
    | exact resolve eq308700 eq4918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918 eq308700
  have eq309199 : ∀ X0 : G, (τ X0) = (k (τ (M.op (M.op X0 X0) X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq308870 X0
       have i₂ := eq34189 X0
       grind)
    | exact superpose eq34189 eq308870
    | (have j0 := eq308870 X0
       grind)
    | exact resolve eq308870 eq34189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34189 eq308870
  have eq309259 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq309199 X0
       have i₂ := eq47 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq47 eq309199
    | (have j0 := eq309199 X0
       grind)
    | exact resolve eq309199 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq309199
  have eq313994 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (τ (k (M.op (M.op X0 X0) X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4830 X0 X1
       have i₂ := eq309259 X0
       grind)
    | exact superpose eq309259 eq4830
    | (have j0 := eq4830 X0 X1
       have j1 := eq309259 X0
       grind)
    | (have r₁ := eq4830 X0 X1
       have r₂ := eq309259 X0
       grind)
    | exact resolve eq4830 eq309259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830 eq309259
  have eq314265 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op (M.op X0 X0) X0) X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq313994 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313994
  have eq340645 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op (M.op (σ X0) (σ X0)) (σ X0)) X0
       have i₂ := eq314265 (σ X0) X1
       grind)
    | exact superpose eq314265 eq35
    | (have j1 := eq314265 (σ X0) X1
       grind)
    | exact resolve eq35 eq314265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq314265
  have eq340950 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ (M.op X0 X0)) (σ X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq340645 X0 X1
       have i₂ := eq4925 X0
       grind)
    | exact superpose eq4925 eq340645
    | (have j0 := eq340645 X0 X1
       grind)
    | exact resolve eq340645 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340645
  have eq341020 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X0 X0) X0))) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq340950 X0 X1
       have i₂ := eq34191 X0
       grind)
    | exact superpose eq34191 eq340950
    | (have j0 := eq340950 X0 X1
       grind)
    | exact resolve eq340950 eq34191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34191 eq340950
  have eq341077 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X0 X0) X0) X0) ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq341020 X0 X1
       have i₂ := eq10 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq10 eq341020
    | (have j0 := eq341020 X0 X1
       grind)
    | exact resolve eq341020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341020
  have eq341119 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (k X1 (τ (σ X0))) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq341077 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq341077
    | (have j0 := eq341077 X0 X1
       grind)
    | exact resolve eq341077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341077
  have eq341157 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq341119 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq341119
    | (have j0 := eq341119 X0 X1
       grind)
    | exact resolve eq341119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341119
  have eq341501 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) ≠ X0 ∨ (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq341157 X0 (M.op (M.op X0 X0) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341157
  have eq341503 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq341501 X0
       grind)
    | (have r₁ := eq341501 X0
       have r₂ := eq20 X0 X0
       grind)
    | exact resolve eq341501 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341501
  have eq341616 : ∀ X0 : G, (k (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq341503 X0
       have i₂ := eq20 X0 X0
       grind)
    | exact superpose eq20 eq341503
    | exact resolve eq341503 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341503
  have eq342475 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq341616 X0
       have i₂ := eq86151 X0 X1
       grind)
    | exact superpose eq86151 eq341616
    | (have j1 := eq86151 X0 X1
       grind)
    | exact resolve eq341616 eq86151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86151 eq341616
  have eq342796 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq342475 X0 X1
       have j1 := eq355 X0 X1
       grind)
    | (have r₁ := eq342475 X0 X1
       have r₂ := eq355 X0 X1
       grind)
    | exact resolve eq342475 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq342475
  have eq343444 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq342796 (σ X1) (σ X0)
       grind)
    | exact superpose eq342796 eq15
    | (have j1 := eq342796 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq342796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343457 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq342796 X1 (τ X0)
       grind)
    | exact superpose eq342796 eq17
    | (have j1 := eq342796 X1 (τ X0)
       grind)
    | exact resolve eq17 eq342796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq342796
  have eq348431 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq343457 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq343457
    | exact resolve eq343457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343457
  have eq349162 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq348431 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq348431
    | (have j0 := eq348431 X0 X1
       grind)
    | exact resolve eq348431 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348431
  have eq357979 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq343444 x y
       grind)
    | exact superpose eq343444 eq16
    | (have j1 := eq343444 x y
       grind)
    | exact resolve eq16 eq343444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343444
  have eq361714 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq357979
       have i₂ := eq349162 x y
       grind)
    | exact superpose eq349162 eq357979
    | (have j1 := eq349162 (σ x) (σ y)
       grind)
    | (have r₁ := eq357979
       have r₂ := eq349162 x y
       grind)
    | exact resolve eq357979 eq349162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349162 eq357979
  have eq361719 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq361714
  have eq361745 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq20 x y
       have i₂ := eq361719
       grind)
    | exact superpose eq361719 eq20
    | exact resolve eq20 eq361719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363077 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq361745
       have i₂ := eq361719
       grind)
    | exact superpose eq361719 eq361745
    | exact resolve eq361745 eq361719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361719 eq361745
  have eq363207 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq363077
  have eq363284 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq20 (σ x) (σ y)
       have i₂ := eq363207
       grind)
    | exact superpose eq363207 eq20
    | exact resolve eq20 eq363207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq364818 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq363284
       have i₂ := eq363207
       grind)
    | exact superpose eq363207 eq363284
    | exact resolve eq363284 eq363207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363207 eq363284
  have eq364992 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq364818
  have eq365038 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq364992
       have i₂ := eq4925 y
       grind)
    | exact superpose eq4925 eq364992
    | exact resolve eq364992 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4925 eq364992
  have eq367057 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq365038
       grind)
    | exact superpose eq365038 eq10
    | exact resolve eq10 eq365038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365038
  have eq367548 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq367057
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq367057
    | exact resolve eq367057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367057
  have eq367549 : y = (M.op y y) := by grind
  clear eq367548
  have eq367599 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq367549
       grind)
    | exact superpose eq367549 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq367549
       grind)
    | exact resolve eq12 eq367549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367626 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4824 y X0
       have i₂ := eq367549
       grind)
    | exact superpose eq367549 eq4824
    | (have j0 := eq4824 y X0
       grind)
    | exact resolve eq4824 eq367549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq367549
  have eq367945 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq367626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367626
  have eq367948 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq367599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367599
  have eq373912 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq367945 (σ X0)
       grind)
    | exact superpose eq367945 eq15
    | exact resolve eq15 eq367945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367945
  have eq374076 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq373912 X0
       have i₂ := eq367948 X0
       grind)
    | exact superpose eq367948 eq373912
    | exact resolve eq373912 eq367948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367948 eq373912
  have eq381975 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq374076 x
       grind)
    | exact superpose eq374076 eq16
    | (have r₁ := eq16
       have r₂ := eq374076 x
       grind)
    | exact resolve eq16 eq374076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374076
  have eq382544 : False := by grind
  exact eq382544

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_x_pxy_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X2 X1))) ≠ X0 ∨ (k (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X2 X1)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) ≠ X0 ∨ (M.op X1 (M.op (M.op X0 X2) (M.op X1 X2))) = (k X1 (M.op (M.op X0 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 X2) (M.op X1 X2))
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 X2) (M.op X1 X2))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq44
    | exact resolve eq44 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq50
    | exact resolve eq50 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq94 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq105 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq101
    | exact resolve eq101 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq105
    | exact resolve eq105 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq145 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq68 sF1
       grind)
    | exact superpose eq68 eq145
    | exact resolve eq145 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq150 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq68 sF0
       grind)
    | exact superpose eq68 eq148
    | exact resolve eq148 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq148
  have eq224 : (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq150 eq42
    | exact resolve eq42 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq150
  have eq240 : (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq224
       have i₂ := eq94 sF1
       grind)
    | exact superpose eq94 eq224
    | exact resolve eq224 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq243 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) := by
    first
    | (have i₁ := eq240
       have i₂ := eq94 sF0
       grind)
    | exact superpose eq94 eq240
    | exact resolve eq240 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq240
  have eq245 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 X1) (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op (M.op x y) (M.op X1 y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 X1) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : x = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op y (σ y)))) := by
    first
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ y) X1)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 X4))) X5) = (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X3 (M.op X2 X4) (M.op X0 X4) X5
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4 X3 X2
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X2 X3) X4
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op y X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 (M.op y X2))
       have i₂ := eq53 X0 X1 X2 y
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq598 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op X2 X1) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op X0 X1) (M.op (M.op X0 y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq600 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X1) (M.op (M.op X0 (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) X1) (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X3 X2 x
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq56 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq721 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq536 eq66
    | exact resolve eq66 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq722 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq537 eq66
    | exact resolve eq66 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1167 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq537 eq67
    | exact resolve eq67 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1213 : ∀ X0 : G, (M.op x (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (σ x)) X0) (M.op (M.op y (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq259 eq53
    | exact resolve eq53 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq259
  have eq1309 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq535 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq535 X0 X1 X2
       grind)
    | exact superpose eq535 eq535
    | exact resolve eq535 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1310 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq535 (M.op X0 X1) (M.op X2 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq535
    | exact resolve eq535 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq55 eq535
    | exact resolve eq535 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1351 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq535 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq535
    | (have j0 := eq535 X0 x y
       grind)
    | exact resolve eq535 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1352 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq535
    | (have j0 := eq535 X0 (σ x) (σ y)
       grind)
    | exact resolve eq535 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1755 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq537 eq640
    | exact resolve eq640 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1776 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq251 eq640
    | exact resolve eq640 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1789 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq640 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq539 X0 X2 X2
       grind)
    | exact superpose eq539 eq640
    | exact resolve eq640 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1795 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq640 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq535 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq535 eq640
    | exact resolve eq640 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1826 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X1)
       have i₂ := eq640 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq640 eq14
    | exact resolve eq14 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2318 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op y X1)) y))) := by
    intro X0 X1
    first
    | exact superpose eq245 eq249
    | exact resolve eq249 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq249
  have eq2410 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2318 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq2318
    | exact resolve eq2318 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2824 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X0 X1) (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq252 eq535
    | exact resolve eq535 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq3058 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) (σ y)))) := by
    first
    | exact superpose eq254 eq257
    | exact resolve eq257 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq257
  have eq3140 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq52 eq3058
    | exact resolve eq3058 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3058
  have eq3148 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1322 eq3140
    | exact resolve eq3140 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq3140
  have eq5090 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op (M.op X0 (M.op y X1)) X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq599 (M.op X0 (M.op y X1)) X1
       have i₂ := eq539 X0 y X1
       grind)
    | exact superpose eq539 eq599
    | exact resolve eq599 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq10036 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq600 x x
       have i₂ := eq1310 (M.op x x) sF3 x
       grind)
    | exact superpose eq1310 eq600
    | exact resolve eq600 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq11731 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op (M.op (M.op X0 y) x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq598
    | exact resolve eq598 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq598
  have eq12828 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) X2 (M.op X2 (M.op X2 X1))
       have i₂ := eq636 X2 X2 X1 X0
       grind)
    | exact superpose eq636 eq14
    | exact resolve eq14 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq20070 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 y) y)) (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq532 eq269
    | exact resolve eq269 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq532
  have eq20180 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq20070 x
       have i₂ := eq640 sF0 x y
       grind)
    | exact superpose eq640 eq20070
    | exact resolve eq20070 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq20070
  have eq25189 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1795 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq535 X0 X2 X1
       grind)
    | exact superpose eq535 eq1795
    | exact resolve eq1795 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq1795
  have eq29081 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2410 eq539
    | exact resolve eq539 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq2410
  have eq54615 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X1) (M.op X2 (σ x))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq251 eq543
    | exact resolve eq543 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq543
  have eq55354 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X1) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq283 eq54615
    | exact resolve eq54615 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq54615
  have eq55696 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op (M.op X0 X1) X1) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq55354 X1 X0
       have i₂ := eq1789 X0 X1 sF4
       grind)
    | exact superpose eq1789 eq55354
    | exact resolve eq55354 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55354
  have eq63274 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq597 X2 (M.op X0 X1) X1 x x
       have i₂ := eq531 X1 x X0 X1 x
       grind)
    | exact superpose eq531 eq597
    | exact resolve eq597 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq597
  have eq83496 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 X4))) X5) = (M.op (M.op X3 (M.op X2 X4)) (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq513 X0 X1 X2 X3 X4 X5
       have i₂ := eq63274 (M.op X0 (M.op X1 X2)) X1 (M.op X3 (M.op X2 X4))
       grind)
    | (have i₁ := eq513 X0 X1 X2 X3 X4 X5
       have i₂ := eq63274 X1 (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq63274 eq513
    | exact resolve eq513 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq149406 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op X2 (M.op (M.op (σ x) (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) X1)))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq605 X0 (M.op X0 (M.op sF4 X0))
       have i₂ := eq83496 X0 sF4 X0 sF2 (M.op sF4 X0) x
       grind)
    | exact superpose eq83496 eq605
    | exact resolve eq605 eq83496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605 eq83496
  have eq149948 : ∀ X0 X1 X2 : G, (M.op X2 (σ y)) = (M.op X2 (M.op X0 (M.op (σ x) (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq149406 X1 X1 X2
       have i₂ := eq63274 (M.op sF2 (M.op X1 (M.op X1 (M.op sF4 X1)))) X1 X2
       grind)
    | (have i₁ := eq149406 X0 X1 X2
       have i₂ := eq63274 X0 (M.op sF2 (M.op X0 (M.op X1 (M.op sF4 X1)))) X2
       grind)
    | exact superpose eq63274 eq149406
    | exact resolve eq149406 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149406
  have eq151106 : ∀ X0 X2 : G, (M.op X2 (σ y)) = (M.op X2 (M.op X0 (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))))) := by
    intro X0 X2
    first
    | (have i₁ := eq149948 X0 X2 X2
       have i₂ := eq1309 X0 sF4 X2
       grind)
    | exact superpose eq1309 eq149948
    | exact resolve eq149948 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149948
  have eq371235 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)))) := by
    intro X0
    first
    | exact superpose eq277 eq2824
    | exact resolve eq2824 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq371236 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | (have i₁ := eq371235 x
       have i₂ := eq63274 (M.op x sF4) sF2 x
       grind)
    | (have i₁ := eq371235 x
       have i₂ := eq63274 sF2 (M.op x sF4) x
       grind)
    | exact superpose eq63274 eq371235
    | exact resolve eq371235 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371235
  have eq401675 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op X0 (M.op (M.op X0 (M.op y X1)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5090 X0 X1
       have i₂ := eq63274 (M.op (M.op X0 (M.op y X1)) X1) X0 x
       grind)
    | (have i₁ := eq5090 X0 X1
       have i₂ := eq63274 X0 (M.op (M.op X0 (M.op y X1)) X1) x
       grind)
    | exact superpose eq63274 eq5090
    | exact resolve eq5090 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5090
  have eq401676 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op X0 (M.op X1 (M.op X0 (M.op y X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq401675 X0 X1
       have i₂ := eq63274 (M.op X0 (M.op y X1)) X1 X0
       grind)
    | (have i₁ := eq401675 X0 X1
       have i₂ := eq63274 X1 (M.op X0 (M.op y X1)) X0
       grind)
    | exact superpose eq63274 eq401675
    | exact resolve eq401675 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401675
  have eq425517 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op X0 (M.op (M.op X0 y) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq11731 X0 X1
       have i₂ := eq63274 (M.op (M.op X0 y) x) X0 X1
       grind)
    | (have i₁ := eq11731 X0 X1
       have i₂ := eq63274 X0 (M.op (M.op X0 y) x) X1
       grind)
    | exact superpose eq63274 eq11731
    | exact resolve eq11731 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11731
  have eq425518 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X1 (M.op X0 (M.op x (M.op X0 y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq425517 X0 X1
       have i₂ := eq63274 (M.op X0 y) x X0
       grind)
    | (have i₁ := eq425517 X0 X1
       have i₂ := eq63274 x (M.op X0 y) X0
       grind)
    | exact superpose eq63274 eq425517
    | exact resolve eq425517 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425517
  have eq726810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq726811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq726810
    | exact resolve eq726810 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726810
  have eq726816 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq726811
       have r₂ := eq28
       grind)
    | exact resolve eq726811 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726811
  have eq726818 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq726816
    | exact resolve eq726816 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq726816
  have eq726820 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq726818 eq1167
    | (have r₁ := eq1167
       have r₂ := eq726818
       grind)
    | exact resolve eq1167 eq726818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq726818
  have eq727151 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq726820
  have eq727682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq727151 eq117
    | exact resolve eq117 eq727151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq727151
  have eq727688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq727682
  have eq727691 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq727688
       have r₂ := eq28
       grind)
    | exact resolve eq727688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727688
  have eq727693 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq727691 eq73
    | exact resolve eq73 eq727691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq727691
  have eq728424 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30 eq727693
    | exact resolve eq727693 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq727693
  have eq728425 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq728424
  have eq728838 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq721
       have i₂ := eq728425
       grind)
    | exact superpose eq728425 eq721
    | (have r₁ := eq721
       have r₂ := eq728425
       grind)
    | exact resolve eq721 eq728425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq728867 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1351 y
       have i₂ := eq728425
       grind)
    | exact superpose eq728425 eq1351
    | exact resolve eq1351 eq728425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351 eq728425
  have eq729164 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by grind
  clear eq728838
  have eq729658 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq729164
       grind)
    | exact superpose eq729164 eq45
    | exact resolve eq45 eq729164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq729164
  have eq729676 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq729658
    | exact resolve eq729658 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq729658
  have eq729753 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq728867 eq29081
    | exact resolve eq29081 eq728867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29081 eq728867
  have eq731083 : (σ (M.op x x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq729753
       grind)
    | exact superpose eq729753 eq107
    | exact resolve eq107 eq729753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq729753
  have eq731775 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq731083
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq731083
    | exact resolve eq731083 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731083
  have eq732613 : (M.op (σ y) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq731775 eq55696
    | exact resolve eq55696 eq731775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55696 eq731775
  have eq732684 : (M.op (σ y) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3148 eq732613
    | exact resolve eq732613 eq3148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148 eq732613
  have eq732960 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1352 eq732684
    | exact resolve eq732684 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq732684
  have eq733456 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq732960 eq722
    | (have r₁ := eq722
       have r₂ := eq732960
       grind)
    | exact resolve eq722 eq732960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq732960
  have eq733785 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq733456
  have eq734311 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq733785 eq729676
    | exact resolve eq729676 eq733785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729676 eq733785
  have eq734316 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq734311
  have eq734318 : y = (M.op x x) := by
    first
    | (have r₁ := eq734316
       have r₂ := eq28
       grind)
    | exact resolve eq734316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734316
  have eq734321 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq734318
       grind)
    | exact superpose eq734318 eq74
    | exact resolve eq74 eq734318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq734435 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op y (σ y))) := by
    first
    | (have i₁ := eq10036 x
       have i₂ := eq734318
       grind)
    | exact superpose eq734318 eq10036
    | exact resolve eq10036 eq734318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10036
  have eq734693 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq12828 X0 x x
       have i₂ := eq734318
       grind)
    | exact superpose eq734318 eq12828
    | exact resolve eq12828 eq734318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734779 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq734693 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq734693
    | (have j0 := eq734693 X0
       grind)
    | exact resolve eq734693 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq734693
  have eq735055 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq734321
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq734321
    | exact resolve eq734321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq734321
  have eq746246 : (M.op x y) = (M.op x (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq734435 eq401676
    | exact resolve eq401676 eq734435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401676 eq734435
  have eq746864 : (M.op x y) = (M.op x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1755 eq746246
    | exact resolve eq746246 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755 eq746246
  have eq747114 : (M.op x y) = (M.op x (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1776 eq746864
    | exact resolve eq746864 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776 eq746864
  have eq747265 : (M.op x y) = (M.op x (σ y)) := by
    first
    | exact superpose eq735055 eq747114
    | exact resolve eq747114 eq735055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735055 eq747114
  have eq761783 : (M.op x (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op x (M.op (M.op y (σ y)) y))) (M.op x y)) := by
    first
    | exact superpose eq1213 eq425518
    | exact resolve eq425518 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq425518
  have eq762311 : (M.op x (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op x y)) (M.op x (M.op (M.op y (σ y)) y))) := by
    first
    | (have i₁ := eq761783
       have i₂ := eq25189 (M.op sF0 sF2) (M.op x (M.op (M.op y sF3) y)) sF0
       grind)
    | (have i₁ := eq761783
       have i₂ := eq25189 (M.op sF0 sF2) sF0 (M.op x (M.op (M.op y sF3) y))
       grind)
    | exact superpose eq25189 eq761783
    | exact resolve eq761783 eq25189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761783
  have eq762801 : (M.op x (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op x y)) (M.op x (σ y))) := by
    first
    | (have i₁ := eq762311
       have i₂ := eq1310 x sF3 y
       grind)
    | exact superpose eq1310 eq762311
    | exact resolve eq762311 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq762311
  have eq763076 : (M.op x (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq747265 eq762801
    | exact resolve eq762801 eq747265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747265 eq762801
  have eq763266 : (M.op x (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (σ x)) (M.op x y)) x) := by
    first
    | exact superpose eq734779 eq763076
    | exact resolve eq763076 eq734779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734779 eq763076
  have eq763384 : (M.op x (M.op (σ x) (σ y))) = (M.op x (σ x)) := by
    first
    | exact superpose eq20180 eq763266
    | exact resolve eq763266 eq20180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20180 eq763266
  have eq763621 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x (M.op (σ x) (M.op x (σ x))))) := by
    intro X0
    first
    | exact superpose eq763384 eq151106
    | exact resolve eq151106 eq763384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151106
  have eq763837 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op x (M.op x (σ x)))) := by
    intro X0
    first
    | exact superpose eq763384 eq12828
    | exact resolve eq12828 eq763384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763384
  have eq763932 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq763837 X0
       have i₂ := eq12828 X0 sF2 x
       grind)
    | exact superpose eq12828 eq763837
    | exact resolve eq763837 eq12828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12828 eq763837
  have eq764088 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq763621 X0
       have i₂ := eq1309 x x sF2
       grind)
    | exact superpose eq1309 eq763621
    | exact resolve eq763621 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763621
  have eq764279 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq764088 X0
       have i₂ := eq734318
       grind)
    | exact superpose eq734318 eq764088
    | exact resolve eq764088 eq734318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734318 eq764088
  have eq764722 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (M.op X0 (σ x))))) := by
    intro X0
    first
    | exact superpose eq763932 eq371236
    | exact resolve eq371236 eq763932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371236
  have eq766276 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq764722 x
       have i₂ := eq1309 x x sF2
       grind)
    | exact superpose eq1309 eq764722
    | exact resolve eq764722 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764722
  have eq769619 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 X1) (M.op (σ y) X1))) (M.op X0 (M.op y y))) := by
    intro X0 X1
    first
    | exact superpose eq764279 eq553
    | exact resolve eq553 eq764279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq764279
  have eq770021 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op X0 (M.op y y))) (M.op (M.op X0 X1) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq769619 X0 X1
       have i₂ := eq25189 sF0 (M.op (M.op X0 X1) (M.op sF3 X1)) (M.op X0 (M.op y y))
       grind)
    | (have i₁ := eq769619 X0 X1
       have i₂ := eq25189 sF0 (M.op X0 (M.op y y)) (M.op (M.op X0 X1) (M.op sF3 X1))
       grind)
    | exact superpose eq25189 eq769619
    | exact resolve eq769619 eq25189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769619
  have eq770808 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 (M.op y y))) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq277 eq770021
    | exact resolve eq770021 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq770021
  have eq771325 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 (M.op y y))) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq770808 X0
       have i₂ := eq63274 (M.op X0 sF4) sF2 (M.op sF0 (M.op X0 (M.op y y)))
       grind)
    | (have i₁ := eq770808 X0
       have i₂ := eq63274 sF2 (M.op X0 sF4) (M.op sF0 (M.op X0 (M.op y y)))
       grind)
    | exact superpose eq63274 eq770808
    | exact resolve eq770808 eq63274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63274 eq770808
  have eq771605 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 (M.op y y))) (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq763932 eq771325
    | exact resolve eq771325 eq763932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763932 eq771325
  have eq771772 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq771605 x
       have i₂ := eq1309 (M.op sF0 (M.op x (M.op y y))) x sF2
       grind)
    | exact superpose eq1309 eq771605
    | exact resolve eq771605 eq1309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309 eq771605
  have eq771862 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq771772 x
       have i₂ := eq25189 sF0 (M.op x (M.op y y)) x
       grind)
    | (have i₁ := eq771772 x
       have i₂ := eq25189 sF0 x (M.op x (M.op y y))
       grind)
    | exact superpose eq25189 eq771772
    | exact resolve eq771772 eq25189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25189 eq771772
  have eq771918 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq771862 X0
       have i₂ := eq1789 X0 (M.op sF0 X0) y
       grind)
    | exact superpose eq1789 eq771862
    | exact resolve eq771862 eq1789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789 eq771862
  have eq800332 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq771918 eq243
    | exact resolve eq243 eq771918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq771918
  have eq801582 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq800332
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq800332
    | exact resolve eq800332 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq800332
  have eq836717 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq801582 eq1826
    | exact resolve eq1826 eq801582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq801582
  have eq837242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq766276 eq836717
    | exact resolve eq836717 eq766276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766276 eq836717
  have eq837444 : False := by grind
  exact eq837444

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pxy_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq44
    | exact resolve eq44 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq50
    | exact resolve eq50 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq93 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq99 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
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
  have eq115 : (M.op x x) = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq142 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq142
    | exact resolve eq142 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq67 sF0
       grind)
    | exact superpose eq67 eq145
    | exact resolve eq145 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq242 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 X1) (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op X0 X1) (M.op y X1))
       have i₂ := eq14 X0 X1 y
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op (M.op x y) (M.op X1 y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ x)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 X1) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op sF3 X1))
       have i₂ := eq14 X0 X1 sF3
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op X1 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq375 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq500 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X3)) = (M.op (M.op (M.op X0 (M.op X3 X2)) (M.op X5 X4)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X0 (M.op X3 X2)) X3 X4 X5
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4) (M.op X3 X4)) = (M.op X0 X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X4 X3 X2
       have i₂ := eq14 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X1) X2 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op X0 X4)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X3 (M.op X2 X4) (M.op X0 X4)
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X2 X3) X4
       have i₂ := eq53 X0 X3 X2 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq56 X2 X0 X1 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) (M.op (σ x) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) (M.op X0 (M.op X5 X2))) (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op X4 X5))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 (M.op X0 (M.op X5 X2)) X3 X4 X5
       have i₂ := eq53 X0 X1 X2 X5
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) X2) (M.op (M.op X2 X1) (σ x))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X3 (M.op X0 (M.op X4 X2))) X5) (M.op (M.op X5 X4) (M.op (M.op X0 X1) (M.op X2 X1)))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X5 X3 (M.op X0 (M.op X4 X2)) X4
       have i₂ := eq53 X0 X1 X2 X4
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X2) X0) (M.op (M.op X0 (M.op X1 X2)) X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X3 X2 x
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq628 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq56 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq657 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq93
    | exact resolve eq93 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq657 X0
       have i₂ := eq10 (M.op X0 X0) X0
       grind)
    | exact superpose eq10 eq657
    | exact resolve eq657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq675 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq670 X0
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq670
    | exact resolve eq670 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq670
  have eq688 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq375 X0 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq375
    | exact resolve eq375 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq375
  have eq725 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq688 X0
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq688
    | exact resolve eq688 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq730 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq725 X0
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq725
    | exact resolve eq725 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1158 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq526
    | exact resolve eq526 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1181 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq526 (M.op X0 X1) X2 (M.op X1 X2)
       have i₂ := eq526 X0 X1 X2
       grind)
    | exact superpose eq526 eq526
    | exact resolve eq526 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq526 (M.op X0 X1) (M.op X2 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq526
    | exact resolve eq526 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq52 eq526
    | exact resolve eq526 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1533 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq628 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq526 X0 X2 X3
       grind)
    | exact superpose eq526 eq628
    | exact resolve eq628 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1536 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (σ y)))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq628
    | exact resolve eq628 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1549 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq247 eq628
    | exact resolve eq628 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1557 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq628
    | (have j0 := eq628 X0 (σ x) (σ y)
       grind)
    | exact resolve eq628 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1567 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq628 (M.op (M.op X0 (M.op X1 X2)) X2) X1 X2
       have i₂ := eq526 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq526 eq628
    | exact resolve eq628 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1975 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op y X1)) y))) := by
    intro X0 X1
    first
    | exact superpose eq242 eq245
    | exact resolve eq245 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq245
  have eq2055 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x x) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1975 X0 x
       have i₂ := eq14 X0 x y
       grind)
    | exact superpose eq14 eq1975
    | exact resolve eq1975 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975
  have eq2307 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1557 (M.op (M.op X0 sF4) sF3)
       have i₂ := eq526 X0 sF4 sF3
       grind)
    | exact superpose eq526 eq1557
    | exact resolve eq1557 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2313 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1557 eq530
    | exact resolve eq530 eq1557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1557
  have eq2648 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (M.op (σ y) X1)) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq248 eq252
    | exact resolve eq252 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq252
  have eq2749 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq2648 X0 x
       have i₂ := eq14 X0 x sF3
       grind)
    | exact superpose eq14 eq2648
    | exact resolve eq2648 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq3695 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq2307 eq526
    | exact resolve eq526 eq2307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq12813 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1184 (M.op (M.op sF3 (M.op x x)) x)
       have i₂ := eq624 sF3 x x (M.op sF3 (M.op x x))
       grind)
    | exact superpose eq624 eq1184
    | exact resolve eq1184 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq1184
  have eq13161 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12813 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12813
    | exact resolve eq12813 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq12813
  have eq19930 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1567 (M.op (M.op X0 X2) X1) X2 X1
       have i₂ := eq526 X0 X2 X1
       grind)
    | exact superpose eq526 eq1567
    | exact resolve eq1567 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq24421 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2055 (M.op x sF0)
       have i₂ := eq1181 (M.op x x) x sF0
       grind)
    | exact superpose eq1181 eq2055
    | exact resolve eq2055 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055
  have eq26221 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2749 (M.op x sF4)
       have i₂ := eq1181 (M.op sF2 sF2) x sF4
       grind)
    | exact superpose eq1181 eq2749
    | exact resolve eq2749 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq28385 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq247 eq575
    | exact resolve eq575 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq28927 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | (have i₁ := eq28385 x
       have i₂ := eq1181 (M.op x (M.op sF4 sF4)) x sF2
       grind)
    | exact superpose eq1181 eq28385
    | exact resolve eq28385 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28385
  have eq29029 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x (M.op (σ x) (σ x))) X0) := by
    intro X0
    first
    | exact superpose eq1549 eq28927
    | exact resolve eq28927 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28927
  have eq33788 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))))) (M.op (σ x) (M.op X2 (M.op X0 (M.op (σ y) (σ x)))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq274 eq602
    | exact resolve eq602 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq34090 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (M.op X2 (σ y)))) = (M.op (M.op X0 (σ x)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq602 eq530
    | exact resolve eq530 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq34306 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))))) (M.op (σ x) (M.op X2 (M.op X0 (M.op (σ x) (σ y)))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq3695 eq33788
    | exact resolve eq33788 eq3695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695 eq33788
  have eq34381 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (σ y))) (M.op (σ x) (M.op X2 (M.op X0 (M.op (σ x) (σ y)))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34306 X0 X1 X2
       have i₂ := eq1181 (M.op X1 X2) (M.op X0 sF3) sF4
       grind)
    | exact superpose eq1181 eq34306
    | exact resolve eq34306 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34306
  have eq39762 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq616 eq628
    | exact resolve eq628 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq39860 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq27 eq39762
    | (have j0 := eq39762 X0 X1
       grind)
    | exact resolve eq39762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39762
  have eq40021 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ x))) X1) X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1549 eq39860
    | exact resolve eq39860 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549 eq39860
  have eq60020 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq585 X2 (M.op X0 X1) X1 x x
       have i₂ := eq522 X1 x X0 X1 x
       grind)
    | exact superpose eq522 eq585
    | exact resolve eq585 eq522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq585
  have eq78365 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X3 X2)) (M.op (M.op X4 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq523 eq503
    | exact resolve eq503 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq523
  have eq79443 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op (M.op (M.op x y) (M.op (M.op X0 X1) y)) X2) (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78365 X0 X1 X2 X1 X2
       have i₂ := eq1182 (M.op (M.op (M.op sF0 (M.op (M.op X0 X1) y)) X2) (M.op X1 X2)) X1 X2
       grind)
    | exact superpose eq1182 eq78365
    | exact resolve eq78365 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq78365
  have eq80518 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 X1) y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79443 X0 X1 X1 x
       have i₂ := eq14 (M.op sF0 (M.op (M.op X0 X1) y)) X1 x
       grind)
    | exact superpose eq14 eq79443
    | exact resolve eq79443 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79443
  have eq80776 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq80518 X0 X1
       have i₂ := eq60020 (M.op X0 X1) y sF0
       grind)
    | (have i₁ := eq80518 X0 X1
       have i₂ := eq60020 y (M.op X0 X1) sF0
       grind)
    | exact superpose eq60020 eq80518
    | exact resolve eq80518 eq60020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80518
  have eq112819 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) (M.op X2 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq603 X2 X3 X1 X0 X1 X3
       have i₂ := eq628 (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1))) (M.op X2 X3) (M.op X1 X3)
       grind)
    | exact superpose eq628 eq603
    | exact resolve eq603 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq112828 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq534 (M.op X2 X2) (M.op X1 X3) X2 (M.op X0 X1) (M.op X3 (M.op X1 X3))
       have i₂ := eq603 X2 X2 (M.op X1 X3) X0 X1 X3
       grind)
    | exact superpose eq603 eq534
    | exact resolve eq534 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq603
  have eq113131 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X2) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq112828 X0 X1 X2 x
       have i₂ := eq1181 (M.op X2 X2) X1 x
       grind)
    | exact superpose eq1181 eq112828
    | exact resolve eq112828 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq112828
  have eq121929 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq535 X0 X1 (M.op X1 X2) (M.op X2 X2) (M.op X1 X1)
       have i₂ := eq617 X1 X2 X2 X0 X1 X1
       grind)
    | exact superpose eq617 eq535
    | exact resolve eq535 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq617
  have eq236093 : (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (k x x) (M.op x x)) := by
    first
    | exact superpose eq50 eq730
    | exact resolve eq730 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq730
  have eq236139 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq236093
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq236093
    | exact resolve eq236093 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236093
  have eq236157 : (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq236139
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq236139
    | exact resolve eq236139 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236139
  have eq236171 : (M.op (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq236157
       have i₂ := eq67 (M.op x x)
       grind)
    | exact superpose eq67 eq236157
    | exact resolve eq236157 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236157
  have eq236185 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq236171
       have i₂ := eq67 (M.op sF2 sF2)
       grind)
    | exact superpose eq67 eq236171
    | exact resolve eq236171 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq236171
  have eq236199 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq26221 eq236185
    | exact resolve eq236185 eq26221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236185
  have eq236212 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq236199
       have i₂ := eq113131 sF4 sF4 sF2
       grind)
    | exact superpose eq113131 eq236199
    | exact resolve eq236199 eq113131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236199
  have eq236223 : (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op x y) (M.op (M.op x x) (M.op x y))) := by
    first
    | (have i₁ := eq236212
       have i₂ := eq24421 (M.op x x)
       grind)
    | exact superpose eq24421 eq236212
    | exact resolve eq236212 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236212
  have eq236233 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq236223
       have i₂ := eq113131 sF0 sF0 x
       grind)
    | exact superpose eq113131 eq236223
    | exact resolve eq236223 eq113131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236223
  have eq236288 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq236233 eq15
    | exact resolve eq15 eq236233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236233
  have eq236341 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq147 eq236288
    | exact resolve eq236288 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236288
  have eq236349 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq236341 eq247
    | exact resolve eq247 eq236341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq236893 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq236349 eq526
    | exact resolve eq526 eq236349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq236349
  have eq248394 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq1158 eq40021
    | exact resolve eq40021 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq40021
  have eq248796 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq27 eq248394
    | (have j0 := eq248394 X0
       grind)
    | exact resolve eq248394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248394
  have eq249429 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) X0) := by
    intro X0
    first
    | exact superpose eq236341 eq248796
    | exact resolve eq248796 eq236341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236341 eq248796
  have eq358337 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq249429 eq500
    | exact resolve eq500 eq249429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq249429
  have eq359313 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq26221 eq358337
    | exact resolve eq358337 eq26221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26221 eq358337
  have eq579433 : (M.op (σ (M.op (M.op x y) (M.op (M.op x (M.op (σ x) (σ x))) y))) (σ (M.op x (M.op (σ x) (σ x))))) = (σ (M.op (M.op (M.op x y) (M.op (M.op x (M.op (σ x) (σ x))) y)) (M.op x (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq29029 eq675
    | exact resolve eq675 eq29029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq29029
  have eq580006 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op (M.op x (M.op (σ x) (σ x))) y))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq51 eq579433
    | exact resolve eq579433 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq579433
  have eq580187 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op y (M.op x (M.op (σ x) (σ x)))))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | (have i₁ := eq580006
       have i₂ := eq60020 (M.op x (M.op sF2 sF2)) y sF0
       grind)
    | (have i₁ := eq580006
       have i₂ := eq60020 y (M.op x (M.op sF2 sF2)) sF0
       grind)
    | exact superpose eq60020 eq580006
    | exact resolve eq580006 eq60020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580006
  have eq580295 : (σ x) = (M.op (σ (M.op (M.op x x) (M.op (σ x) (σ x)))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq80776 eq580187
    | exact resolve eq580187 eq80776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80776 eq580187
  have eq580362 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op (M.op (σ x) (σ x)) (M.op x y)))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | (have i₁ := eq580295
       have i₂ := eq24421 (M.op sF2 sF2)
       grind)
    | exact superpose eq24421 eq580295
    | exact resolve eq580295 eq24421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421 eq580295
  have eq580404 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | (have i₁ := eq580362
       have i₂ := eq113131 sF0 sF0 sF2
       grind)
    | exact superpose eq113131 eq580362
    | exact resolve eq580362 eq113131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580362
  have eq580432 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq147 eq580404
    | exact resolve eq580404 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq580404
  have eq580452 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x (M.op (σ x) (σ x))))) := by
    first
    | (have i₁ := eq580432
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq580432
    | exact resolve eq580432 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580432
  have eq631702 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq359313 eq530
    | exact resolve eq530 eq359313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq359313
  have eq632243 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ (M.op x y)) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq631702 x
       have i₂ := eq19930 sF1 (M.op sF1 x) x
       grind)
    | (have i₁ := eq631702 x
       have i₂ := eq19930 sF1 x (M.op sF1 x)
       grind)
    | exact superpose eq19930 eq631702
    | exact resolve eq631702 eq19930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631702
  have eq632551 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq632243 X0
       have i₂ := eq19930 (M.op sF1 X0) (M.op sF1 X0) sF4
       grind)
    | (have i₁ := eq632243 X0
       have i₂ := eq19930 (M.op sF1 X0) sF4 (M.op sF1 X0)
       grind)
    | exact superpose eq19930 eq632243
    | exact resolve eq632243 eq19930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632243
  have eq782682 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (σ y))) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq632551 x
       have i₂ := eq60020 sF1 x (M.op (M.op sF1 x) sF4)
       grind)
    | (have i₁ := eq632551 X0
       have i₂ := eq60020 X0 sF1 (M.op (M.op sF1 X0) sF4)
       grind)
    | exact superpose eq60020 eq632551
    | exact resolve eq632551 eq60020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632551
  have eq1023529 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq580452
       have i₂ := eq121929 x x sF2
       grind)
    | (have i₁ := eq580452
       have i₂ := eq121929 x sF2 x
       grind)
    | exact superpose eq121929 eq580452
    | exact resolve eq580452 eq121929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121929 eq580452
  have eq1149432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X3)) (M.op X2 (M.op X3 X1))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq112819 X0 X1 X2 X3
       have i₂ := eq19930 (M.op X0 X1) (M.op X2 (M.op X3 X1)) (M.op X2 X3)
       grind)
    | (have i₁ := eq112819 X0 X1 X2 X3
       have i₂ := eq19930 (M.op X0 X1) (M.op X2 X3) (M.op X2 (M.op X3 X1))
       grind)
    | exact superpose eq19930 eq112819
    | exact resolve eq112819 eq19930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19930 eq112819
  have eq1166407 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x (M.op X1 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq1023529 eq113131
    | exact resolve eq113131 eq1023529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113131 eq1023529
  have eq1583310 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x x) (M.op X0 X1)) (M.op X0 (M.op X1 x))) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq1149432 y x X0 X1
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq1149432
    | exact resolve eq1149432 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1583316 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1583310 x x
       have i₂ := eq1149432 x x x x
       grind)
    | exact superpose eq1149432 eq1583310
    | exact resolve eq1583310 eq1149432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149432 eq1583310
  have eq2153817 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) X2)) = (M.op (M.op X0 (σ x)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq1536 eq34090
    | exact resolve eq34090 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq34090
  have eq2167973 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op (M.op X0 (σ y)) (M.op X2 (M.op X0 (M.op (σ x) (σ y)))))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq2153817 eq34381
    | exact resolve eq34381 eq2153817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34381 eq2153817
  have eq2167974 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op X0 (M.op (σ y) (M.op X2 (M.op X0 (M.op (σ x) (σ y))))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2167973 X0 X1 X2
       have i₂ := eq1533 X0 (M.op (M.op X1 X2) sF2) sF3 (M.op X2 (M.op X0 sF4))
       grind)
    | exact superpose eq1533 eq2167973
    | exact resolve eq2167973 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq2167973
  have eq7912071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1583316 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1583316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583316
  have eq7912088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq7912071
    | exact resolve eq7912071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7912071
  have eq7912103 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq7912088
       have r₂ := eq28
       grind)
    | exact resolve eq7912088 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7912088
  have eq7912635 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq7912103 eq2167974
    | exact resolve eq2167974 eq7912103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7912103
  have eq7912990 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f7912990_15 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = x := by
      intro X0
      grind
    have f7912990_16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (σ x)) (M.op X0 (M.op (σ y) (M.op X2 (M.op X0 (M.op (σ x) (σ y))))))) = X1 := by
      intro X0 X1 X2
      grind
    have f7912990_25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
    have f7912990_26 : (σ y) ≠ (σ x) := by grind
    have f7912990_27 : y ≠ (M.op x x) := by grind
    have f7912990_28 : y ≠ x := by grind
    have f7912990_31 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))))) ∨ y = (M.op x x) ∨ y = x := by
      intro X0
      first
      | (have j0 := f7912990_15 X0
         grind)
      | (have r₁ := f7912990_15 X0
         have r₂ := f7912990_25
         grind)
      | exact resolve f7912990_15 f7912990_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7912990_32 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))))) ∨ y = x := by
      intro X0
      first
      | (have j0 := f7912990_31 X0
         grind)
      | (have r₁ := f7912990_31 X0
         have r₂ := f7912990_27
         grind)
      | exact resolve f7912990_31 f7912990_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7912990_33 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op X0 (M.op (σ y) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))))) := by
      intro X0
      first
      | (have j0 := f7912990_32 X0
         grind)
      | (have r₁ := f7912990_32 X0
         have r₂ := f7912990_28
         grind)
      | exact resolve f7912990_32 f7912990_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7912990_34 : (σ y) = (σ x) := by
      first
      | (have i₁ := f7912990_33 x
         have i₂ := f7912990_16 x (σ x) (σ x)
         grind)
      | exact superpose f7912990_16 f7912990_33
      | exact resolve f7912990_33 f7912990_16
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f7912990_35 : False := by
      first
      | (have r₁ := f7912990_34
         have r₂ := f7912990_26
         grind)
      | exact resolve f7912990_34 f7912990_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f7912990_35
  clear eq2167974 eq7912635
  have eq7915322 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq7912990 eq72
    | exact resolve eq72 eq7912990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq7912990
  have eq7916890 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq30 eq7915322
    | exact resolve eq7915322 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915322
  have eq7916891 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7916890
  have eq7918064 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq7916891
       grind)
    | exact superpose eq7916891 eq73
    | exact resolve eq73 eq7916891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq7918389 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1166407 X0 x
       have i₂ := eq7916891
       grind)
    | exact superpose eq7916891 eq1166407
    | exact resolve eq1166407 eq7916891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166407 eq7916891
  have eq7919460 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7918389 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7918389
    | (have j0 := eq7918389 X0
       grind)
    | exact resolve eq7918389 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7918389
  have eq7919659 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq7918064
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq7918064
    | exact resolve eq7918064 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7918064
  have eq7919996 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq21 eq7919460
    | (have j0 := eq7919460 X0
       grind)
    | exact resolve eq7919460 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7919460
  have eq8218192 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq7919996 eq7919659
    | exact resolve eq7919659 eq7919996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7919659 eq7919996
  have eq8218440 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8218192
  have eq8224566 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq8218440 eq782682
    | exact resolve eq782682 eq8218440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782682 eq8218440
  have eq8225579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2313 eq8224566
    | exact resolve eq8224566 eq2313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313 eq8224566
  have eq8225984 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8225579
       have r₂ := eq28
       grind)
    | exact resolve eq8225579 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8225579
  have eq8226896 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq8225984 eq30
    | exact resolve eq30 eq8225984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8225984
  have eq8227712 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq8226896
    | exact resolve eq8226896 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8226896
  have eq8227713 : x = y := by grind
  clear eq8227712
  have eq8228243 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq8227713
       grind)
    | exact superpose eq8227713 eq19
    | exact resolve eq19 eq8227713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq8228244 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq8227713
       grind)
    | exact superpose eq8227713 eq25
    | exact resolve eq25 eq8227713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq8227713
  have eq8229148 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8228244
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8228244
    | exact resolve eq8228244 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq8228244
  have eq8231390 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq13161 x
       have i₂ := eq8228243
       grind)
    | exact superpose eq8228243 eq13161
    | exact resolve eq13161 eq8228243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13161 eq8228243
  have eq8232603 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq21 eq8231390
    | exact resolve eq8231390 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq8231390
  have eq8233224 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq8232603
       have i₂ := eq60020 sF3 sF1 sF2
       grind)
    | (have i₁ := eq8232603
       have i₂ := eq60020 sF1 sF3 sF2
       grind)
    | exact superpose eq60020 eq8232603
    | exact resolve eq8232603 eq60020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60020 eq8232603
  have eq8233649 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq8229148 eq8233224
    | exact resolve eq8233224 eq8229148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8229148 eq8233224
  have eq8233925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq236893 eq8233649
    | exact resolve eq8233649 eq236893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236893 eq8233649
  have eq8234109 : False := by grind
  exact eq8234109

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pxx_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X1 X2) (M.op X0 X2)) X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) (M.op X0 X2)) X0
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X1 X2) (M.op X0 X2)) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have r₂ := eq9 X0 X1 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X2 X3)) = X1 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq30 (M.op X1 X2) X3 X2 x
       have i₂ := eq9 X1 X2 x
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq30 X0 x X2 X1
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq84 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X1 X2) (M.op X0 X2) X0
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X2 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 (M.op X1 X0) X2 (M.op X0 X2)
       have i₂ := eq70 X1 X0 X2
       grind)
    | exact superpose eq70 eq70
    | exact resolve eq70 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 (M.op X0 X1) X2 (M.op (M.op X0 X1) X1)
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq84
    | exact resolve eq84 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 (σ X0) (σ X1)
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq133 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq72 X1 X0 X0
       grind)
    | exact superpose eq72 eq133
    | exact resolve eq133 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq133
  have eq301 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq231 X1 X2 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq231 eq9
    | exact resolve eq9 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq451 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq428 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq843 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq451 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq1678 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 y x
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 y x
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq1749 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2111 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq843 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq2122 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2111 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq2111
    | exact resolve eq2111 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2125 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2122 X0
       have i₂ := eq2111 X0
       grind)
    | exact superpose eq2111 eq2122
    | exact resolve eq2122 eq2111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq2122
  have eq2214 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq231 (σ X0) X2 X1
       have i₂ := eq2125 X0
       grind)
    | exact superpose eq2125 eq231
    | exact resolve eq231 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq5106 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1678
       have i₂ := eq2125 x
       grind)
    | exact superpose eq2125 eq1678
    | exact resolve eq1678 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq5110 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5106
       have i₂ := eq126 y x
       grind)
    | exact superpose eq126 eq5106
    | (have j1 := eq126 y x
       grind)
    | exact resolve eq5106 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq5106
  have eq5111 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5110
  have eq5120 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5111
       grind)
    | exact superpose eq5111 eq10
    | exact resolve eq10 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq5147 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5120
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5120
    | exact resolve eq5120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5120
  have eq5148 : y = (M.op x x) := by grind
  clear eq5147
  have eq5169 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2214 x X1 X0
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq2214
    | exact resolve eq2214 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq5180 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq70 x x X0
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq70
    | exact resolve eq70 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5181 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq70 X0 x x
       have i₂ := eq5148
       grind)
    | exact superpose eq5148 eq70
    | exact resolve eq70 eq5148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq5148
  have eq5264 : ∀ X0 X1 : G, (M.op X1 (M.op y X0)) = (M.op X1 (M.op (M.op x X0) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (M.op y X0) X1 (M.op x X0)
       have i₂ := eq5180 X0
       grind)
    | exact superpose eq5180 eq85
    | exact resolve eq85 eq5180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5180
  have eq5284 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op y X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5264 X0 X1
       have i₂ := eq84 x X1 X0
       grind)
    | exact superpose eq84 eq5264
    | exact resolve eq5264 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq5264
  have eq5595 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq5181 (M.op X0 (M.op X1 X1))
       have i₂ := eq301 X0 X1 x
       grind)
    | exact superpose eq301 eq5181
    | exact resolve eq5181 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq5181
  have eq11021 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1749 X0 X1
       have i₂ := eq5595 X0 (M.op X0 X1)
       grind)
    | exact superpose eq5595 eq1749
    | exact resolve eq1749 eq5595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749 eq5595
  have eq11070 : ∀ X0 : G, (M.op (σ X0) y) = (k (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11021 (σ X0) (σ X0)
       have i₂ := eq2125 X0
       grind)
    | exact superpose eq2125 eq11021
    | exact resolve eq11021 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11124 : ∀ X0 : G, (M.op (σ X0) y) = (k (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11070 X0
       have i₂ := eq2125 (M.op X0 X0)
       grind)
    | exact superpose eq2125 eq11070
    | exact resolve eq11070 eq2125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125 eq11070
  have eq11138 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq11124 X0
       have i₂ := eq15 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       grind)
    | exact superpose eq15 eq11124
    | exact resolve eq11124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11124
  have eq11141 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq11138 X0
       have i₂ := eq11021 X0 X0
       grind)
    | exact superpose eq11021 eq11138
    | exact resolve eq11138 eq11021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11021 eq11138
  have eq14149 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq5169 y X0
       have i₂ := eq5284 (σ y) X0
       grind)
    | exact superpose eq5284 eq5169
    | exact resolve eq5169 eq5284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5169 eq5284
  have eq14422 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14149 (σ x)
       grind)
    | exact superpose eq14149 eq16
    | exact resolve eq16 eq14149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14149
  have eq14442 : False := by grind
  exact eq14442

/-- `Equation2688`: `x = ((x ◇ y) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pxx_pyx_Equation2688 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2688 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2688.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 (M.op X0 (M.op X1 X1)) X1
       have r₂ := eq13 X0 (M.op X1 X1)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq125 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 (M.op X3 X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X2 X2)) X1 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X2
       have i₂ := eq16 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (σ x) (M.op X1 X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq28 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X1) (M.op X2 X2)) X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) (M.op (M.op X1 X0) (M.op X2 X2))) = X0 ∨ (k X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq28 X0 (M.op (M.op X1 X0) (M.op X2 X2))
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op (M.op X1 X0) (M.op X2 X2))
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq585
       grind)
    | exact superpose eq585 eq40
    | exact resolve eq40 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq592 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq591
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq591
    | exact resolve eq591 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq594 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq592
    | exact resolve eq592 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq594 eq587
    | exact resolve eq587 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq611 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq604
       have r₂ := eq27
       grind)
    | exact resolve eq604 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq618 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq611 eq16
    | exact resolve eq16 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq611 eq178
    | exact resolve eq178 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq611 eq176
    | exact resolve eq176 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) X1) = X0 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq611 eq16
    | exact resolve eq16 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq620 eq618
    | exact resolve eq618 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq657 : (σ x) ≠ (σ x) ∨ (k (M.op (σ y) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq624 eq13
    | (have j0 := eq13 (M.op (σ y) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ y) (σ y)) (σ x)
       have r₂ := eq624
       grind)
    | exact resolve eq13 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op X0 X0)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq624 eq16
    | exact resolve eq16 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq659 : (k (M.op (σ y) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq657
  have eq660 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq620 eq658
    | exact resolve eq658 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq661 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq620 eq659
    | exact resolve eq659 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq662 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq660
    | exact resolve eq660 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq663 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq661
    | exact resolve eq661 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq667 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) (M.op X0 X0)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq662 eq16
    | exact resolve eq16 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq668 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq620 eq667
    | exact resolve eq667 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq673 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X1 X1)) (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq621 eq177
    | exact resolve eq177 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq694 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (M.op X2 X2)) X1) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq611 eq177
    | exact resolve eq177 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 x
       have i₂ := eq177 X0 X2 x X1
       grind)
    | (have i₁ := eq16 X0 (M.op x x) X2
       have i₂ := eq177 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq177 (M.op X0 X1) X1 X2 x
       grind)
    | (have i₁ := eq16 X0 (M.op X2 X2) X2
       have i₂ := eq177 (M.op X0 (M.op X2 X2)) (M.op X2 X2) X2 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq176 x
       have i₂ := eq177 sF4 sF3 x x
       grind)
    | exact superpose eq177 eq176
    | exact resolve eq176 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ y)) X1) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq620 eq694
    | exact resolve eq694 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq754 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq681 X0 x
       have i₂ := eq16 sF4 sF3 x
       grind)
    | exact superpose eq16 eq681
    | exact resolve eq681 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq764 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op X1 X1))) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq754 (M.op X0 X0)
       have i₂ := eq178 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq754 (M.op X0 X0)
       have i₂ := eq178 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq178 eq754
    | exact resolve eq754 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq786 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (σ y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq620 eq764
    | exact resolve eq764 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq936 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (M.op X1 X1)) (σ x)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq668 eq177
    | exact resolve eq177 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq943 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq936 X0 x
       have i₂ := eq734 sF3 sF3 x
       grind)
    | exact superpose eq734 eq936
    | exact resolve eq936 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1032 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq943 eq176
    | exact resolve eq176 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq943
  have eq1248 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) X1) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq749 eq623
    | exact resolve eq623 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1259 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (σ y)) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq749 eq623
    | exact resolve eq623 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq1270 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (σ y)) = X0 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq1259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1275 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) X1) = X0 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq1248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq1572 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq1270 eq1275
    | exact resolve eq1275 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1578 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ x) X0) X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1032 eq1275
    | exact resolve eq1275 eq1032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1635 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ x) X0) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1638 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1572 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572
  have eq5484 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq611 eq673
    | exact resolve eq673 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq5541 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq594 eq5484
    | exact resolve eq5484 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5484
  have eq5571 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5541 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5541
       grind)
    | exact resolve eq13 eq5541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5541
  have eq5584 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq5571
  have eq5601 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq5584
    | exact resolve eq5584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5584
  have eq5608 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq594 eq5601
    | exact resolve eq5601 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5601
  have eq5610 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq5608
       have r₂ := eq27
       grind)
    | exact resolve eq5608 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608
  have eq5624 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq5610 eq1275
    | exact resolve eq1275 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5636 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq5610 eq620
    | exact resolve eq620 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5640 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5610 eq786
    | exact resolve eq786 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq5648 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5610 eq13
    | exact resolve eq13 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5650 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5610 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5654 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5610 eq1270
    | exact resolve eq1270 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5656 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq5610 eq1638
    | exact resolve eq1638 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5657 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq5656 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq5659 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq5654
  have eq5668 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq5640
  have eq5671 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq5636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5636
  have eq5674 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq5624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5624
  have eq5690 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq5648
       have r₂ := eq5650
       grind)
    | exact resolve eq5648 eq5650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5648 eq5650
  have eq5786 : (τ (σ (M.op x y))) = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5690 eq116
    | exact resolve eq116 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq5690
  have eq5797 : (M.op x y) = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq5786
    | exact resolve eq5786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5786
  have eq5843 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq573 y y X0
       have i₂ := eq5797
       grind)
    | exact superpose eq5797 eq573
    | (have j0 := eq573 y y x
       grind)
    | exact resolve eq573 eq5797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5844 : y = (M.op y y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq175 eq5843
    | exact resolve eq5843 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq5843
  have eq5882 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X0)) = (M.op (M.op (M.op (σ (M.op x y)) (σ y)) (M.op X1 X1)) (σ y)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq5659 eq177
    | exact resolve eq177 eq5659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5659
  have eq5915 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5882 X0 x
       have i₂ := eq16 sF1 sF3 x
       grind)
    | exact superpose eq16 eq5882
    | exact resolve eq5882 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5882
  have eq5995 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ (M.op x y))) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq5671 eq1275
    | exact resolve eq1275 eq5671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq6029 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ (M.op x y))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq5995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5995
  have eq6166 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5671 eq5674
    | exact resolve eq5674 eq5671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6254 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq6166
  have eq6344 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5671 eq5915
    | exact resolve eq5915 eq5671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6350 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5610 eq5915
    | exact resolve eq5915 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5915
  have eq6384 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq6350
  have eq6387 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq6344
  have eq6416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6384 eq13
    | (have j0 := eq13 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ y) (σ (M.op x y))
       have r₂ := eq6384
       grind)
    | exact resolve eq13 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384
  have eq6433 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq6416
  have eq6653 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6433 eq5668
    | exact resolve eq5668 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq6656 : (σ y) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6433 eq6254
    | exact resolve eq6254 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6657 : (σ (M.op x y)) = (M.op (σ y) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6433 eq6387
    | exact resolve eq6387 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6387
  have eq6690 : (σ (M.op x y)) = (M.op (σ y) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by grind
  clear eq6657
  have eq6691 : (σ y) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq6656
  have eq6694 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by grind
  clear eq6653
  have eq6825 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq6690 eq1638
    | exact resolve eq1638 eq6690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638 eq6690
  have eq6826 : ∀ X0 : G, (M.op (M.op (σ y) X0) X0) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq6825 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6825
  have eq6834 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5657 eq6826
    | exact resolve eq6826 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657 eq6826
  have eq6843 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6433 eq6834
    | exact resolve eq6834 eq6433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6433 eq6834
  have eq6860 : (k (σ y) (σ (M.op x y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6691 eq623
    | exact resolve eq623 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6871 : (k (σ y) (σ (M.op x y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq6860
  have eq6879 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq5610 eq6871
    | exact resolve eq6871 eq5610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5610 eq6871
  have eq7206 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6694 eq1635
    | exact resolve eq1635 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq7216 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6694 eq1270
    | exact resolve eq1270 eq6694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6694
  have eq7223 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq7216
  have eq7227 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by grind
  clear eq7206
  have eq7280 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6879 eq13
    | exact resolve eq13 eq6879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7282 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6879 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq6879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6879
  have eq7323 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq7280
       have r₂ := eq7282
       grind)
    | exact resolve eq7280 eq7282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7280 eq7282
  have eq7349 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7323 eq134
    | exact resolve eq134 eq7323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq7361 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq7349
    | exact resolve eq7349 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7349
  have eq7435 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq5844
       grind)
    | exact superpose eq5844 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq5844
       grind)
    | exact resolve eq13 eq5844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7442 : y = (M.op (M.op y y) (σ y)) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1270 y y
       have i₂ := eq5844
       grind)
    | exact superpose eq5844 eq1270
    | exact resolve eq1270 eq5844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq7449 : y = (M.op (M.op y y) (σ y)) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq7442
  have eq7452 : y = (k y y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq7435
  have eq7468 : y = (M.op y (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq5844 eq7449
    | exact resolve eq7449 eq5844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449
  have eq7473 : y = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq5797 eq7452
    | exact resolve eq7452 eq5797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5797 eq7452
  have eq8737 : y = (M.op (M.op y (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq7468 eq6029
    | exact resolve eq6029 eq7468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6029
  have eq8809 : y = (M.op (M.op y (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq8737
  have eq8845 : y = (M.op y (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq7468 eq8809
    | exact resolve eq8809 eq7468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7468 eq8809
  have eq8868 : (M.op x y) = (M.op (M.op x y) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq7473 eq8845
    | exact resolve eq8845 eq7473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8845
  have eq8915 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq8868 eq5671
    | exact resolve eq5671 eq8868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5671 eq8868
  have eq8934 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq8915
  have eq9091 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 X0)) (M.op y (M.op X0 X0))) ∨ y = (k y (M.op y (M.op X0 X0))) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq581 y y x
       have i₂ := eq5844
       grind)
    | exact superpose eq5844 eq581
    | exact resolve eq581 eq5844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq5844
  have eq9313 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op (M.op x y) (M.op X0 X0))) ∨ y = (k y (M.op y (M.op X0 X0))) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq7473 eq9091
    | (have j0 := eq9091 X0
       grind)
    | exact resolve eq9091 eq7473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9091
  have eq9438 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op (M.op x y) (M.op X0 X0))) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op X0 X0))) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq7473 eq9313
    | (have j0 := eq9313 X0
       grind)
    | exact resolve eq9313 eq7473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7473 eq9313
  have eq9541 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) (M.op X0 X0))) ∨ x = y ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq620 eq9438
    | (have j0 := eq9438 X0
       grind)
    | exact resolve eq9438 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9438
  have eq9608 : (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) (σ y))) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq620 eq9541
    | exact resolve eq9541 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq9541
  have eq9651 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) (σ y))) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq8934 eq9608
    | exact resolve eq9608 eq8934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9608
  have eq9663 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq8934 eq9651
    | exact resolve eq9651 eq8934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934 eq9651
  have eq9670 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have j1 := eq589 (M.op x y)
       grind)
    | (have r₁ := eq9663
       have r₂ := eq589 (M.op x y)
       grind)
    | exact resolve eq9663 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9663
  have eq9756 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq9670 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq9670
       grind)
    | exact resolve eq13 eq9670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9670
  have eq9770 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq9756
  have eq9869 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq9770 eq42
    | exact resolve eq42 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq9879 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq9869
    | exact resolve eq9869 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9869
  have eq10219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq9879 eq572
    | (have j0 := eq572 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq572 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq9879
       grind)
    | exact resolve eq572 eq9879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq9879
  have eq10221 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq10219
  have eq10222 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq10221
  have eq10364 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq10222 eq5674
    | exact resolve eq5674 eq10222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10400 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq10222 eq623
    | exact resolve eq623 eq10222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq10222
  have eq10411 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq10400
  have eq10428 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq10364
  have eq10437 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq6254 eq10411
    | exact resolve eq10411 eq6254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6254 eq10411
  have eq10733 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10428 eq5674
    | exact resolve eq5674 eq10428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5674 eq10428
  have eq10795 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq10733
  have eq10815 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10437 eq10795
    | exact resolve eq10795 eq10437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10437 eq10795
  have eq10984 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X1) X1) := by
    intro X1
    first
    | exact superpose eq737 eq721
    | exact resolve eq721 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11874 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq10815 eq663
    | exact resolve eq663 eq10815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq10815
  have eq11969 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq11874
  have eq11989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq594 eq11969
    | exact resolve eq11969 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11969
  have eq11997 : y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq11989
       have r₂ := eq27
       grind)
    | exact resolve eq11989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11989
  have eq12002 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) X1) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq11997
       grind)
    | exact superpose eq11997 eq16
    | exact resolve eq16 eq11997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12021 : y = (k x x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq11997
       grind)
    | exact superpose eq11997 eq28
    | exact resolve eq28 eq11997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12027 : y = (k x x) ∨ x = y := by grind
  clear eq12021
  have eq12418 : x = (M.op (M.op y y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq12002 x x
       have i₂ := eq11997
       grind)
    | exact superpose eq11997 eq12002
    | exact resolve eq12002 eq11997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12595 : x = (M.op (M.op y y) x) ∨ x = y := by grind
  clear eq12418
  have eq12661 : (M.op y y) = (M.op (M.op x y) x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq12002 (M.op y y) x
       have i₂ := eq12595
       grind)
    | exact superpose eq12595 eq12002
    | exact resolve eq12002 eq12595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12002 eq12595
  have eq12662 : (M.op y y) = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq12661
  have eq12665 : (M.op y y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq12662
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12662
    | exact resolve eq12662 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12662
  have eq12718 : y ≠ (M.op (M.op x y) x) ∨ (k y y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq12665
       grind)
    | exact superpose eq12665 eq13
    | exact resolve eq13 eq12665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12720 : (k y y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq12665
       grind)
    | exact superpose eq12665 eq28
    | exact resolve eq28 eq12665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12665
  have eq12745 : (k y y) = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have r₁ := eq12718
       have r₂ := eq12720
       grind)
    | exact resolve eq12718 eq12720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12718 eq12720
  have eq19501 : (k (σ y) (σ (M.op x y))) ≠ (k (σ y) (σ (M.op x y))) ∨ (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6843 eq13
    | (have j0 := eq13 (σ (M.op x y)) (k (σ y) (σ (M.op x y)))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (k (σ y) (σ (M.op x y)))
       have r₂ := eq6843
       grind)
    | exact resolve eq13 eq6843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6843
  have eq19525 : (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by grind
  clear eq19501
  have eq19544 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6691 eq19525
    | exact resolve eq19525 eq6691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6691 eq19525
  have eq19556 : (τ (σ y)) = (k (M.op x y) (τ (k (σ y) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19544 eq125
    | exact resolve eq125 eq19544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq19562 : (τ (σ y)) = (k (M.op x y) (k y (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq19556
    | exact resolve eq19556 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq19556
  have eq19564 : y = (k (M.op x y) (k y (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq19562
    | exact resolve eq19562 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19562
  have eq19565 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7361 eq19564
    | exact resolve eq19564 eq7361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7361 eq19564
  have eq19566 : x = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11997 eq19565
    | exact resolve eq19565 eq11997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11997 eq19565
  have eq20107 : (σ x) = (k (σ (M.op x y)) (σ (k (M.op x y) (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19566 eq38
    | exact resolve eq38 eq19566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq19566
  have eq20112 : (σ x) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq42 eq20107
    | exact resolve eq20107 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq20107
  have eq20114 : (σ x) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq20112
    | exact resolve eq20112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20112
  have eq20115 : (σ x) = (k (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20114
    | exact resolve eq20114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20114
  have eq20116 : (σ x) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7323 eq20115
    | exact resolve eq20115 eq7323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7323 eq20115
  have eq20119 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20116 eq19544
    | exact resolve eq19544 eq20116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19544 eq20116
  have eq20123 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq20119
  have eq24998 : (σ x) ≠ (σ y) ∨ (k (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7223 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) (σ y)
       grind)
    | exact resolve eq13 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7223
  have eq25048 : (k (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y)))) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (k (σ y) (σ (M.op x y))))) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq24998
       have r₂ := eq20123
       grind)
    | exact resolve eq24998 eq20123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24998
  have eq25073 : (k (M.op (σ y) (σ x)) (σ y)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op x x) := by
    first
    | exact superpose eq7227 eq25048
    | exact resolve eq25048 eq7227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7227 eq25048
  have eq25083 : (M.op (σ x) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ x)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20123 eq25073
    | exact resolve eq25073 eq20123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20123 eq25073
  have eq25087 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq611 eq25083
    | exact resolve eq25083 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq25083
  have eq25090 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq25087
    | exact resolve eq25087 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25087
  have eq25093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq594 eq25090
    | exact resolve eq25090 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq25090
  have eq25095 : y = (M.op x x) := by
    first
    | (have r₁ := eq25093
       have r₂ := eq27
       grind)
    | exact resolve eq25093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25093
  have eq25171 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq16
    | exact resolve eq16 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25175 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op X0 y) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2 x
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq177
    | exact resolve eq177 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq25177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 x X1
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq178
    | exact resolve eq178 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq25188 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq721 X0 x X1
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq721
    | exact resolve eq721 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq25191 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq734 X0 X1 x
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq734
    | exact resolve eq734 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25193 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) y) := by
    first
    | (have i₁ := eq737 x
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq737
    | exact resolve eq737 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25207 : x ≠ y ∨ y = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq13
    | exact resolve eq13 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25208 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq16 x x X0
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq16
    | exact resolve eq16 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25095
  have eq25219 : y = (k x x) := by
    first
    | (have r₁ := eq25207
       have r₂ := eq12027
       grind)
    | exact resolve eq25207 eq12027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12027 eq25207
  have eq25221 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25175 X0 X1 x
       have i₂ := eq25177 (M.op X0 X1) x
       grind)
    | exact superpose eq25177 eq25175
    | exact resolve eq25175 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25175
  have eq25225 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq25219
       grind)
    | exact superpose eq25219 eq40
    | exact resolve eq40 eq25219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25219
  have eq25232 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq25225
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25225
    | exact resolve eq25225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25225
  have eq25234 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq25232
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25232
    | exact resolve eq25232 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25232
  have eq25241 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25234 eq589
    | (have j0 := eq589 (σ x)
       grind)
    | exact resolve eq589 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq25243 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq25234 eq573
    | (have j0 := eq573 (σ x) (σ x) x
       grind)
    | exact resolve eq573 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq25244 : (σ x) = (M.op (M.op (σ y) y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25243 x
       have i₂ := eq25177 sF3 x
       grind)
    | exact superpose eq25177 eq25243
    | exact resolve eq25243 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25243
  have eq25248 : (σ x) = (M.op (M.op (σ y) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq25244
       have i₂ := eq25221 sF3 sF2
       grind)
    | exact superpose eq25221 eq25244
    | exact resolve eq25244 eq25221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25244
  have eq26464 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq25188 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25188
    | (have j0 := eq25188 x X0
       grind)
    | exact resolve eq25188 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26768 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq26464 eq734
    | exact resolve eq734 eq26464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq26464
  have eq26821 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq26768 X0 x
       have i₂ := eq25177 (M.op x X0) x
       grind)
    | exact superpose eq25177 eq26768
    | exact resolve eq26768 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26768
  have eq27394 : ∀ X0 : G, x ≠ x ∨ (k (M.op y (M.op X0 X0)) x) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op y (M.op X0 X0)) x
       have i₂ := eq25208 X0
       grind)
    | exact superpose eq25208 eq13
    | (have j0 := eq13 (M.op y (M.op X0 X0)) x
       grind)
    | (have r₁ := eq13 (M.op y (M.op X0 X0)) x
       have r₂ := eq25208 X0
       grind)
    | exact resolve eq13 eq25208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27414 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq25191 (M.op y (M.op X0 X0)) x
       have i₂ := eq25208 X0
       grind)
    | exact superpose eq25208 eq25191
    | exact resolve eq25191 eq25208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25208
  have eq27415 : ∀ X0 : G, (k (M.op y (M.op X0 X0)) x) = (M.op x (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq27394 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27394
  have eq27416 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq27414 X0
       have i₂ := eq26821 x
       grind)
    | exact superpose eq26821 eq27414
    | exact resolve eq27414 eq26821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26821 eq27414
  have eq27427 : (M.op x (M.op y y)) = (k (M.op y y) x) := by
    first
    | (have i₁ := eq27415 x
       have i₂ := eq25177 y x
       grind)
    | exact superpose eq25177 eq27415
    | exact resolve eq27415 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27415
  have eq27447 : (M.op y y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq27416 x
       have i₂ := eq25177 y x
       grind)
    | exact superpose eq25177 eq27416
    | exact resolve eq27416 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27416
  have eq27458 : (M.op x y) = (k (M.op y y) x) := by
    first
    | (have i₁ := eq27427
       have i₂ := eq25177 x y
       grind)
    | exact superpose eq25177 eq27427
    | exact resolve eq27427 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27427
  have eq27475 : (M.op x y) = (k (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq27458
       have i₂ := eq27447
       grind)
    | exact superpose eq27447 eq27458
    | exact resolve eq27458 eq27447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27458
  have eq27482 : (M.op x y) = (k (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq27475
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27475
    | exact resolve eq27475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27475
  have eq27554 : y ≠ (M.op (M.op x y) x) ∨ (k y y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq27447
       grind)
    | exact superpose eq27447 eq13
    | exact resolve eq13 eq27447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27556 : (k y y) = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq27447
       grind)
    | exact superpose eq27447 eq28
    | exact resolve eq28 eq27447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27447
  have eq27580 : (k y y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq12745 eq27556
    | exact resolve eq27556 eq12745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27556
  have eq27582 : x ≠ (M.op (M.op x y) x) ∨ (k y y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq12745 eq27554
    | exact resolve eq27554 eq12745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12745 eq27554
  have eq27620 : (k y y) = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq27582
       have r₂ := eq27580
       grind)
    | exact resolve eq27582 eq27580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27580 eq27582
  have eq27638 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) x)) (σ x)) := by
    first
    | exact superpose eq27482 eq40
    | exact resolve eq40 eq27482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq27482
  have eq27643 : (σ (M.op x y)) = (k (σ (k y y)) (σ x)) := by
    first
    | exact superpose eq27620 eq27638
    | exact resolve eq27638 eq27620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27620 eq27638
  have eq27645 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq27643
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq27643
    | exact resolve eq27643 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq27643
  have eq27647 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq27645
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27645
    | exact resolve eq27645 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27645
  have eq27649 : (σ (M.op x y)) = (k (k (σ y) (σ y)) (σ x)) := by
    first
    | exact superpose eq20 eq27647
    | exact resolve eq27647 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq27647
  have eq32079 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) y) := by
    intro X0
    first
    | exact superpose eq25193 eq25221
    | exact resolve eq25221 eq25193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25193
  have eq34501 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (M.op (M.op (σ x) X0) y) y) := by
    intro X0
    first
    | exact superpose eq32079 eq25191
    | exact resolve eq25191 eq32079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32079
  have eq43859 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25248 eq25171
    | exact resolve eq25171 eq25248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25171
  have eq43900 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) y) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25248 eq25191
    | exact resolve eq25191 eq25248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25248
  have eq43903 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10984 eq43900
    | exact resolve eq43900 eq10984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43900
  have eq43961 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43859 eq737
    | exact resolve eq737 eq43859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43990 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq43859 eq25177
    | exact resolve eq25177 eq43859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44044 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43903 eq43961
    | exact resolve eq43961 eq43903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43961
  have eq46767 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (σ x)) (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43903 eq25191
    | exact resolve eq25191 eq43903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43903
  have eq46772 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44044 eq46767
    | exact resolve eq46767 eq44044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46767
  have eq46825 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq46772 eq25188
    | exact resolve eq25188 eq46772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25188
  have eq46828 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X0) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq46772 eq25221
    | exact resolve eq25221 eq46772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25221 eq46772
  have eq204577 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43859 eq46828
    | exact resolve eq46828 eq43859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43859 eq46828
  have eq205018 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq204577
       have r₂ := eq25241
       grind)
    | exact resolve eq204577 eq25241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204577
  have eq205124 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43990 eq205018
    | exact resolve eq205018 eq43990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205018
  have eq205217 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq205124 eq46825
    | exact resolve eq46825 eq205124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46825 eq205124
  have eq205265 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq205217
  have eq205392 : (σ x) ≠ (σ x) ∨ (k (M.op (σ y) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq205265 eq13
    | (have j0 := eq13 (M.op (σ y) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ y) (σ y)) (σ x)
       have r₂ := eq205265
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq205265
       grind)
    | exact resolve eq13 eq205265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205437 : (k (M.op (σ y) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq205392
  have eq205474 : (k (M.op (σ y) (σ y)) (σ x)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq205437
       have i₂ := eq25177 sF2 sF3
       grind)
    | exact superpose eq25177 eq205437
    | exact resolve eq205437 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205437
  have eq205496 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43990 eq205474
    | exact resolve eq205474 eq43990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43990 eq205474
  have eq205513 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq205496
    | exact resolve eq205496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205496
  have eq205534 : (M.op (σ x) (σ y)) = (k (k (σ y) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq205513
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq205513
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq205513 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq205546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27649 eq205534
    | exact resolve eq205534 eq27649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205534
  have eq205551 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq205546
       have r₂ := eq27
       grind)
    | exact resolve eq205546 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205546
  have eq205564 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq205551 eq205265
    | exact resolve eq205265 eq205551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205265
  have eq205565 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq205551 eq205513
    | exact resolve eq205513 eq205551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205513
  have eq205704 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq205551 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq205551
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq205551
       grind)
    | exact resolve eq13 eq205551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205551
  have eq205748 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq205704
  have eq205750 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq205565
  have eq205751 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq205564
  have eq205947 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq205748 eq27649
    | exact resolve eq27649 eq205748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205748
  have eq206013 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq205751 eq44044
    | exact resolve eq44044 eq205751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44044 eq205751
  have eq206066 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq206013
  have eq206103 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq206066
    | exact resolve eq206066 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206066
  have eq206157 : (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) = (M.op (M.op (σ x) y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206103 eq34501
    | exact resolve eq34501 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34501
  have eq206168 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq206103 eq185
    | exact resolve eq185 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq206201 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206103 eq737
    | exact resolve eq737 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq206254 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq206103 eq25177
    | exact resolve eq25177 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206280 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206103 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq206103
       grind)
    | exact resolve eq13 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206299 : (σ x) = (M.op (M.op (σ x) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206103 eq25191
    | exact resolve eq25191 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206320 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq206280
  have eq206341 : (σ x) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206103 eq206299
    | exact resolve eq206299 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206299
  have eq206355 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25234 eq206320
    | exact resolve eq206320 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206320
  have eq206403 : (M.op (M.op (σ x) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq206168 x
       have i₂ := eq25177 sF4 x
       grind)
    | exact superpose eq25177 eq206168
    | exact resolve eq206168 eq25177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25177 eq206168
  have eq206410 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10984 eq206157
    | exact resolve eq206157 eq10984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10984 eq206157
  have eq206464 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206103 eq206403
    | exact resolve eq206403 eq206103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206103 eq206403
  have eq206467 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206201 eq206410
    | exact resolve eq206410 eq206201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206201 eq206410
  have eq206507 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq206464
    | exact resolve eq206464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq206464
  have eq206508 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206355 eq206467
    | exact resolve eq206467 eq206355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206355 eq206467
  have eq207574 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206507 eq25191
    | exact resolve eq25191 eq206507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25191 eq206507
  have eq207604 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206254 eq207574
    | exact resolve eq207574 eq206254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206254 eq207574
  have eq207647 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206508 eq207604
    | exact resolve eq207604 eq206508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206508 eq207604
  have eq207660 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq206341 eq207647
    | exact resolve eq207647 eq206341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206341 eq207647
  have eq207661 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq207660
  have eq207675 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq207661 eq27
    | exact resolve eq27 eq207661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207661
  have eq210351 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq205947 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq205947
       grind)
    | exact resolve eq13 eq205947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205947
  have eq210391 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq210351
  have eq210426 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25234 eq210391
    | exact resolve eq210391 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210391
  have eq210702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq210426 eq205750
    | exact resolve eq205750 eq210426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205750 eq210426
  have eq210721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq210702
       have r₂ := eq25241
       grind)
    | exact resolve eq210702 eq25241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25241 eq210702
  have eq210727 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq210721
       have r₂ := eq27
       grind)
    | exact resolve eq210721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq210721
  have eq210865 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq210727 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq210727
       grind)
    | exact resolve eq13 eq210727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210727
  have eq210905 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq210865
  have eq211235 : (σ x) = (σ y) := by
    first
    | exact superpose eq210905 eq25234
    | exact resolve eq25234 eq210905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210905
  have eq211439 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq211235 eq27649
    | exact resolve eq27649 eq211235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27649
  have eq211602 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq25234 eq211439
    | exact resolve eq211439 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211439
  have eq211689 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq211235 eq211602
    | exact resolve eq211602 eq211235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211602
  have eq211749 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25234 eq211689
    | exact resolve eq211689 eq25234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25234 eq211689
  have eq211795 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq211235 eq211749
    | exact resolve eq211749 eq211235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211235 eq211749
  have eq211822 : False := by grind
  exact eq211822

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_pxy_pyx_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y
       grind)
    | exact resolve eq15 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq177
    | exact resolve eq177 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq630 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) (k X0 X1)) X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op (M.op X2 X1) (k X0 X1)) X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : (M.op x y) = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq651
       grind)
    | exact superpose eq651 eq40
    | exact resolve eq40 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq673
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq673
    | exact resolve eq673 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq676 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq674
    | exact resolve eq674 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq699 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq676 eq659
    | exact resolve eq659 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq720
       have r₂ := eq27
       grind)
    | exact resolve eq720 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq734 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq727 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq727
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq727
       grind)
    | exact resolve eq12 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq727 eq177
    | exact resolve eq177 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq734
  have eq740 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq727 eq736
    | exact resolve eq736 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq736
  have eq742 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq676 eq739
    | exact resolve eq739 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq744 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq740
    | exact resolve eq740 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq748 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq744
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq744
       grind)
    | exact resolve eq12 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq750 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq177
    | exact resolve eq177 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : y = (M.op x x) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq748
  have eq754 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq744 eq750
    | exact resolve eq750 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq750
  have eq757 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq754
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq754
    | exact resolve eq754 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq761 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq757 eq187
    | exact resolve eq187 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq765 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq761
    | exact resolve eq761 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq767 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq757 eq765
    | exact resolve eq765 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq772 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq767 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq767
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq767
       grind)
    | exact resolve eq12 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq772
  have eq1024 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq742 eq181
    | exact resolve eq181 eq742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq1033 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq1024
    | exact resolve eq1024 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq676 eq1033
    | exact resolve eq1033 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq1033
  have eq1039 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1038
       have r₂ := eq27
       grind)
    | exact resolve eq1038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1045 : y = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq177
    | exact resolve eq177 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1039 eq1045
    | exact resolve eq1045 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039 eq1045
  have eq1052 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1049
    | exact resolve eq1049 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1053 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1052 eq29
    | exact resolve eq29 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1057 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1052 eq117
    | exact resolve eq117 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1060 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1052 eq133
    | exact resolve eq133 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1052
  have eq1067 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq1060
    | exact resolve eq1060 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1060
  have eq1070 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq1057
    | exact resolve eq1057 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1057
  have eq1074 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1053
    | exact resolve eq1053 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1077 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq18
    | exact resolve eq18 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1078 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq24
    | exact resolve eq24 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1078
    | exact resolve eq1078 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1117 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1077 eq186
    | exact resolve eq186 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq1119 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1077 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq1077
       grind)
    | exact resolve eq12 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1124 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1119
  have eq1188 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq651
       have i₂ := eq1070
       grind)
    | exact superpose eq1070 eq651
    | exact resolve eq651 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq1070
  have eq1193 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1074 eq1188
    | exact resolve eq1188 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1200 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq757 eq699
    | (have r₁ := eq699
       have r₂ := eq757
       grind)
    | exact resolve eq699 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1201 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1200
  have eq1523 : (M.op x y) = (k y x) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq753
       grind)
    | exact superpose eq753 eq181
    | exact resolve eq181 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1535 : (M.op x y) = (k y x) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1523
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1523
    | exact resolve eq1523 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1543 : (M.op x y) = (k (M.op x y) x) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq757 eq1535
    | exact resolve eq1535 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1549 : (M.op x y) = (k (M.op x y) x) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq757 eq1543
    | exact resolve eq1543 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1598 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1201 eq91
    | exact resolve eq91 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1201
  have eq1601 : y = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq1598
    | exact resolve eq1598 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1605 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1067 eq1601
    | exact resolve eq1601 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1611 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1549 eq40
    | exact resolve eq40 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1612 : x ≠ (M.op x y) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1549
  have eq1613 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1611
    | exact resolve eq1611 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1621 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq777 eq181
    | exact resolve eq181 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1631 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1621
    | exact resolve eq1621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1634 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq757 eq1631
    | exact resolve eq1631 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq1631
  have eq1655 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1605 eq181
    | exact resolve eq181 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq1665 : (σ x) = (k (σ x) (σ y)) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq767 eq1655
    | exact resolve eq1655 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1655
  have eq1672 : (σ y) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090 eq1613
    | exact resolve eq1613 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1680 : (σ y) = (k (σ y) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1672
       have r₂ := eq1612
       grind)
    | exact resolve eq1672 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq1672
  have eq1743 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1634 eq142
    | exact resolve eq142 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1634
  have eq1745 : y = (k y x) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq1743
    | exact resolve eq1743 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1743
  have eq1749 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1074 eq1745
    | exact resolve eq1745 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq1809 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (k (M.op x y) y)) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq630 x y X0
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq630
    | (have j0 := eq630 (M.op x y) y X0
       grind)
    | exact resolve eq630 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1855 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op (M.op (M.op X0 y) (k (M.op x y) y)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1809 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1809
    | (have j0 := eq1809 X0
       grind)
    | exact resolve eq1809 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1856 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (k (M.op x y) y)) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1855 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq2097 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1665 eq153
    | exact resolve eq153 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1665
  have eq2102 : x = (k x y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq2097
    | exact resolve eq2097 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097
  have eq2106 : (M.op x y) = (k (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1074 eq2102
    | exact resolve eq2102 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2102
  have eq2121 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1124 eq36
    | exact resolve eq36 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1124
  have eq2126 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2121
    | exact resolve eq2121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq2128 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090 eq2126
    | exact resolve eq2126 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2133 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1680 eq659
    | exact resolve eq659 eq1680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq2139 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq2133
  have eq2217 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1749 eq108
    | exact resolve eq108 eq1749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1749
  have eq2223 : x = (k y x) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq2217
    | exact resolve eq2217 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2217
  have eq2227 : (M.op x y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1074 eq2223
    | exact resolve eq2223 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq2223
  have eq2325 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2139 eq177
    | exact resolve eq177 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2329 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq2139 eq2325
    | exact resolve eq2325 eq2139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2139 eq2325
  have eq2335 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq2329
    | exact resolve eq2329 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2329
  have eq2336 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2335
  have eq2342 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2336 eq38
    | exact resolve eq38 eq2336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2336
  have eq2351 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2342
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2342
    | exact resolve eq2342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2353 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090 eq2351
    | exact resolve eq2351 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2363 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2351 eq630
    | (have j0 := eq630 (M.op (M.op X0 (σ x)) (σ x)) (σ x) x
       grind)
    | exact resolve eq630 eq2351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq2351
  have eq2377 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2353 eq659
    | exact resolve eq659 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq2353
  have eq3027 : y = (M.op (M.op y (k (M.op x y) y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1856 (k (M.op y y) y)
       have i₂ := eq581 y
       grind)
    | exact superpose eq581 eq1856
    | exact resolve eq1856 eq581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq3029 : y = (M.op (M.op (M.op x y) (k (M.op x y) y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1856 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1856
    | (have j0 := eq1856 x
       grind)
    | exact resolve eq1856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq3048 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2106 eq3027
    | exact resolve eq3027 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027
  have eq3065 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) := by grind
  clear eq3048
  have eq3118 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2377 eq177
    | exact resolve eq177 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3124 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2377 eq3118
    | exact resolve eq3118 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377 eq3118
  have eq3129 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3124
    | exact resolve eq3124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3130 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3129
  have eq3131 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3130 eq27
    | exact resolve eq27 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3144 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3131
       have r₂ := eq1090
       grind)
    | exact resolve eq3131 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq3150 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3144 eq27
    | exact resolve eq27 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3151 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3144 eq176
    | exact resolve eq176 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq3152 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3144 eq179
    | exact resolve eq179 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq3162 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090 eq3150
    | exact resolve eq3150 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3165 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq3162
  have eq3193 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (k X0 (σ y))) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3151 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq3151
    | (have j1 := eq28 (M.op (σ x) (k X0 (σ y))) (σ y)
       grind)
    | exact resolve eq3151 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3237 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3152 eq3152
    | exact resolve eq3152 eq3152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3253 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3237
  have eq5458 : y = (M.op (k (M.op x y) y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3065
       have i₂ := eq28 sF0 y
       grind)
    | exact superpose eq28 eq3065
    | (have j1 := eq28 (k (M.op x y) y) y
       grind)
    | exact resolve eq3065 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3065
  have eq5481 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq2106 eq5458
    | exact resolve eq5458 eq2106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106 eq5458
  have eq5482 : y = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq5481
  have eq5485 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5482 eq3029
    | exact resolve eq3029 eq5482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq5498 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq5485
  have eq5848 : y = (M.op (k y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq5498
       have i₂ := eq28 y sF0
       grind)
    | exact superpose eq28 eq5498
    | (have j1 := eq28 (k y (M.op x y)) y
       grind)
    | exact resolve eq5498 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5498
  have eq5871 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2227 eq5848
    | exact resolve eq5848 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227 eq5848
  have eq5872 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1193 eq5871
    | exact resolve eq5871 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq5871
  have eq5873 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq5872
  have eq5884 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq5873 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq5873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5873
  have eq5895 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq5884
  have eq5908 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5895 eq5482
    | exact resolve eq5482 eq5895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482 eq5895
  have eq5918 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq5908
  have eq13067 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2363 eq2363
    | exact resolve eq2363 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq13102 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13067
  have eq13964 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2128 eq3193
    | (have j0 := eq3193 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq3193 eq2128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128
  have eq14001 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13964
  have eq14007 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq14001
    | exact resolve eq14001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14001
  have eq14011 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq14007
    | exact resolve eq14007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14007
  have eq14013 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3130 eq14011
    | exact resolve eq14011 eq3130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3130 eq14011
  have eq14014 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq14013
    | exact resolve eq14013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14013
  have eq14015 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq14014
  have eq14016 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3144 eq14015
    | exact resolve eq14015 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14015
  have eq14017 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14016
       have r₂ := eq3165
       grind)
    | exact resolve eq14016 eq3165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14016
  have eq14065 : (k x (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14017 eq181
    | exact resolve eq181 eq14017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq14017
  have eq14097 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1117 eq14065
    | exact resolve eq14065 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq14065
  have eq14182 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14097 eq42
    | exact resolve eq42 eq14097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq14097
  have eq14194 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14182
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14182
    | exact resolve eq14182 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14182
  have eq14198 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1090 eq14194
    | exact resolve eq14194 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq14194
  have eq14241 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14198 eq3193
    | (have j0 := eq3193 (M.op (σ x) (σ x))
       grind)
    | exact resolve eq3193 eq14198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3193 eq14198
  have eq14247 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14241
  have eq14254 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14247
    | exact resolve eq14247 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14247
  have eq14267 : (σ x) = (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3144 eq14254
    | exact resolve eq14254 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14254
  have eq14275 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14267
       have r₂ := eq3165
       grind)
    | exact resolve eq14267 eq3165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14267
  have eq14277 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3253 eq14275
    | exact resolve eq14275 eq3253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253 eq14275
  have eq14278 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq14277
    | exact resolve eq14277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14277
  have eq14279 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3144 eq14278
    | exact resolve eq14278 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3144 eq14278
  have eq14280 : x = (M.op x y) := by
    first
    | (have r₁ := eq14279
       have r₂ := eq3165
       grind)
    | exact resolve eq14279 eq3165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165 eq14279
  have eq14281 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14280
       grind)
    | exact superpose eq14280 eq18
    | exact resolve eq18 eq14280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14282 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq14280
       grind)
    | exact superpose eq14280 eq22
    | exact resolve eq22 eq14280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14280
  have eq14361 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14282 eq20
    | exact resolve eq20 eq14282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq14478 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14281 eq5918
    | exact resolve eq5918 eq14281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5918 eq14281
  have eq14515 : y = (M.op x y) := by grind
  clear eq14478
  have eq14529 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14515
       grind)
    | exact superpose eq14515 eq24
    | exact resolve eq24 eq14515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14515
  have eq14554 : (σ x) = (σ y) := by
    first
    | exact superpose eq14282 eq14529
    | exact resolve eq14529 eq14282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14282 eq14529
  have eq14562 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14554 eq26
    | exact resolve eq26 eq14554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14818 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14562 eq13102
    | exact resolve eq13102 eq14562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13102
  have eq14858 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14361 eq14818
    | exact resolve eq14818 eq14361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14818
  have eq14863 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14562 eq14858
    | exact resolve eq14858 eq14562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14562 eq14858
  have eq14864 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14863
  have eq14870 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14554 eq14864
    | exact resolve eq14864 eq14554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14554 eq14864
  have eq14871 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14870
  have eq14877 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq14871 eq27
    | exact resolve eq27 eq14871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14871
  have eq14902 : False := by grind
  exact eq14902

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq44
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq44 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118 eq92
    | (have j0 := eq92 (σ x) (σ y)
       grind)
    | exact resolve eq92 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq121
    | exact resolve eq121 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq122
       have r₂ := eq27
       grind)
    | exact resolve eq122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq27
    | exact resolve eq27 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127 eq51
    | exact resolve eq51 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq231 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq327 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq127 eq54
    | exact resolve eq54 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq337 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq327 eq327
    | exact resolve eq327 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq343 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq337
  have eq347 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq343 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq343
       grind)
    | exact resolve eq13 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 : G, (M.op X0 (σ x)) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq347 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq426 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq351 eq49
    | exact resolve eq49 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq351
  have eq429 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq75
    | (have r₁ := eq75
       have r₂ := eq127
       grind)
    | exact resolve eq75 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq430 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq429
  have eq435 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq343 eq426
    | exact resolve eq426 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq426
  have eq439 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq435
  have eq441 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq439
    | exact resolve eq439 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq439
  have eq443 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq43
       have i₂ := eq441
       grind)
    | exact superpose eq441 eq43
    | exact resolve eq43 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq447 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq443
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq443
    | exact resolve eq443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq888 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq430 eq221
    | exact resolve eq221 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq430
  have eq910 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq888
  have eq916 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq910
    | exact resolve eq910 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq917 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq127 eq916
    | exact resolve eq916 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq926 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq917
  have eq927 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq926
    | exact resolve eq926 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq930 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq927 eq118
    | exact resolve eq118 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq934 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq930
  have eq939 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq934
       have r₂ := eq129
       grind)
    | exact resolve eq934 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq947 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq939 eq127
    | exact resolve eq127 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq939
  have eq955 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq947
  have eq968 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq955 eq118
    | exact resolve eq118 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq955
  have eq996 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq968
  have eq1103 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq996 eq447
    | exact resolve eq447 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq996
  have eq1108 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1103
  have eq1112 : x = (M.op x y) := by
    first
    | (have r₁ := eq1108
       have r₂ := eq129
       grind)
    | exact resolve eq1108 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1108
  have eq1114 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1112 eq20
    | exact resolve eq20 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1116 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) := by
    intro X0
    first
    | exact superpose eq1112 eq50
    | exact resolve eq50 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1117 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) x) x) := by
    intro X0
    first
    | exact superpose eq1112 eq53
    | exact resolve eq53 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1119 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq1112 eq74
    | (have r₁ := eq74
       have r₂ := eq1112
       grind)
    | exact resolve eq74 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1123 : x = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1112 eq231
    | exact resolve eq231 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq1124 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq1119
  have eq1130 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1114
    | exact resolve eq1114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq1131 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1130 eq26
    | exact resolve eq26 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1235 : x = (M.op x x) := by
    first
    | (have i₁ := eq1117 x
       have i₂ := eq1123
       grind)
    | exact superpose eq1123 eq1117
    | exact resolve eq1117 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq1123
  have eq1259 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1235
       grind)
    | exact superpose eq1235 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1235
       grind)
    | exact resolve eq13 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1259 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1268 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1265 x
       grind)
    | exact superpose eq1265 eq43
    | exact resolve eq43 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1265
  have eq1275 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1268
       have i₂ := eq1235
       grind)
    | exact superpose eq1235 eq1268
    | exact resolve eq1268 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq1268
  have eq1278 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1130 eq1275
    | exact resolve eq1275 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1280 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1278
    | exact resolve eq1278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq1282 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1130 eq1280
    | exact resolve eq1280 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1286 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1282 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq1287 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1286
  have eq2462 : y = (M.op (M.op x y) y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1116 y
       have i₂ := eq1124
       grind)
    | exact superpose eq1124 eq1116
    | exact resolve eq1116 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116 eq1124
  have eq2473 : y = (M.op (M.op x y) y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2462
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2462
    | exact resolve eq2462 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462
  have eq2476 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1112 eq2473
    | exact resolve eq2473 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2479 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2476
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2476
    | exact resolve eq2476 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2476
  have eq2481 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1112 eq2479
    | exact resolve eq2479 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq2479
  have eq2486 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq2481
       grind)
    | exact superpose eq2481 eq44
    | exact resolve eq44 eq2481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2481
  have eq2493 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1130 eq2486
    | exact resolve eq2486 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2495 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2493
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2493
    | exact resolve eq2493 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq2496 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1130 eq2495
    | exact resolve eq2495 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq2503 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2496 eq92
    | (have j0 := eq92 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq92 eq2496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2496
  have eq2504 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq2503
  have eq2506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1131 eq2504
    | exact resolve eq2504 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq2509 : x = y := by
    first
    | (have r₁ := eq2506
       have r₂ := eq27
       grind)
    | exact resolve eq2506 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq2514 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2509
       grind)
    | exact superpose eq2509 eq24
    | exact resolve eq24 eq2509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2509
  have eq2538 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2514
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2514
    | exact resolve eq2514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2514
  have eq2547 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1130 eq2538
    | exact resolve eq2538 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq2538
  have eq2587 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2547 eq1131
    | exact resolve eq1131 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131 eq2547
  have eq2592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1287 eq2587
    | exact resolve eq2587 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq2587
  have eq2603 : False := by grind
  exact eq2603
