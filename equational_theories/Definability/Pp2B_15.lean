import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq342 (σ X0)
       grind)
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq422 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq61
    | exact resolve eq61 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1061 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq431 X0 (σ X1)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X0 (σ X1)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1112 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1061 X0 (τ X1)
       grind)
    | exact superpose eq1061 eq17
    | (have j1 := eq1061 X0 (τ X1)
       grind)
    | exact resolve eq17 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1061
  have eq1318 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1318 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1318
    | (have j0 := eq1318 X0 X1
       grind)
    | exact resolve eq1318 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318
  have eq1888 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1072 x y
       grind)
    | exact superpose eq1072 eq16
    | (have j1 := eq1072 x y
       grind)
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1993 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq1390 y x
       grind)
    | exact superpose eq1390 eq1888
    | (have j1 := eq1390 (σ y) (σ x)
       grind)
    | (have r₁ := eq1888
       have r₂ := eq1390 y x
       grind)
    | exact resolve eq1888 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq1994 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1993
  have eq2000 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq61
    | exact resolve eq61 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994
  have eq2036 : x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2000 (M.op x x)
       have i₂ := eq2000 x
       grind)
    | exact superpose eq2000 eq2000
    | exact resolve eq2000 eq2000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2051 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2036
  have eq2057 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq422 x (σ y)
       have i₂ := eq2051
       grind)
    | exact superpose eq2051 eq422
    | exact resolve eq422 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq2062 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 (σ y) (σ x) X0
       have i₂ := eq2051
       grind)
    | exact superpose eq2051 eq61
    | exact resolve eq61 eq2051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2051
  have eq2233 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2062 (σ (M.op x x))
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq2062
    | exact resolve eq2062 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057 eq2062
  have eq2251 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2233
  have eq2254 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2251
       have i₂ := eq376 x
       grind)
    | exact superpose eq376 eq2251
    | exact resolve eq2251 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2251
  have eq2266 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq430 x X0
       have i₂ := eq2254
       grind)
    | exact superpose eq2254 eq430
    | (have j0 := eq430 x X0
       grind)
    | (have r₁ := eq430 x x
       have r₂ := eq2254
       grind)
    | exact resolve eq430 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254
  have eq2294 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq2266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2297 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq2294 X0
       have j1 := eq430 x X0
       grind)
    | (have r₁ := eq2294 X0
       have r₂ := eq430 x x
       grind)
    | exact resolve eq2294 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2294
  have eq2306 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2297 (σ X0)
       grind)
    | exact superpose eq2297 eq15
    | exact resolve eq15 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2412 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2306 y
       grind)
    | exact superpose eq2306 eq16
    | exact resolve eq16 eq2306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq2514 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2412
       have i₂ := eq1390 y x
       grind)
    | exact superpose eq1390 eq2412
    | (have j1 := eq1390 y x
       grind)
    | (have r₁ := eq2412
       have r₂ := eq1390 y x
       grind)
    | exact resolve eq2412 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq2515 : x = (M.op y x) := by grind
  clear eq2514
  have eq2523 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq2515
       grind)
    | exact superpose eq2515 eq61
    | exact resolve eq61 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2515
  have eq2554 : x = (M.op x x) := by
    first
    | (have i₁ := eq2523 (M.op x x)
       have i₂ := eq2523 x
       grind)
    | exact superpose eq2523 eq2523
    | exact resolve eq2523 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq2578 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq92 x x
       have i₂ := eq2554
       grind)
    | exact superpose eq2554 eq92
    | (have r₁ := eq92 x x
       have r₂ := eq2554
       grind)
    | exact resolve eq92 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2554
  have eq2613 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq2578 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2670 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2412
       have i₂ := eq2613 y
       grind)
    | exact superpose eq2613 eq2412
    | exact resolve eq2412 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq2613
  have eq2673 : False := by grind
  exact eq2673

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq275 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq277 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | (have j0 := eq275 X0
       grind)
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq280 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq286 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq280 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq280
    | (have j0 := eq280 (τ X0)
       grind)
    | exact resolve eq280 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X1 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq439 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq2862 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq78 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2863 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2862 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq2869 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2863 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2863
    | (have j0 := eq2863 X0
       grind)
    | exact resolve eq2863 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2871 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2869 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2869
    | exact resolve eq2869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869
  have eq2910 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2871 X0
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq2871
    | (have j0 := eq2871 X0
       grind)
    | exact resolve eq2871 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2871
  have eq2915 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2910 X0
       grind)
    | exact superpose eq2910 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2910 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2910 X0
       grind)
    | exact resolve eq12 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910
  have eq2941 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2915 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq3159 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq2941 X0 X1
       grind)
    | exact superpose eq2941 eq11
    | (have j1 := eq2941 X0 X1
       grind)
    | exact resolve eq11 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941
  have eq3236 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3159 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3159
    | (have j0 := eq3159 X0 X0
       grind)
    | exact resolve eq3159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3159
  have eq3360 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3236 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236
  have eq3361 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3360 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq3477 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq3361 X0
       grind)
    | exact superpose eq3361 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq3478 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq3361 X0
       grind)
    | exact superpose eq3361 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq3481 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq3361 X0
       grind)
    | exact superpose eq3361 eq286
    | (have j0 := eq286 X0
       grind)
    | exact resolve eq286 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq3511 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3361 (σ X0)
       grind)
    | exact superpose eq3361 eq15
    | exact resolve eq15 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3518 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq3361 (τ X0)
       grind)
    | exact superpose eq3361 eq43
    | exact resolve eq43 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3566 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3518 X0
       have i₂ := eq3361 X0
       grind)
    | exact superpose eq3361 eq3518
    | exact resolve eq3518 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3518
  have eq3573 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3511 X0
       have i₂ := eq3361 X0
       grind)
    | exact superpose eq3361 eq3511
    | exact resolve eq3511 eq3361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3361 eq3511
  have eq3833 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq3573 X0
       grind)
    | exact superpose eq3573 eq34
    | exact resolve eq34 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3843 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (σ X0) (σ X0)
       have i₂ := eq3573 X0
       grind)
    | exact superpose eq3573 eq19
    | exact resolve eq19 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5297 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3481 (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq3481
    | (have j0 := eq3481 (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | exact resolve eq3481 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq3481
  have eq5314 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5297
  have eq5329 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5314 X0 X1
       have i₂ := eq3566 (σ X0)
       grind)
    | exact superpose eq3566 eq5314
    | (have j0 := eq5314 X0 X1
       grind)
    | exact resolve eq5314 eq3566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3566 eq5314
  have eq5346 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5329 X0 X1
       have i₂ := eq3573 X0
       grind)
    | exact superpose eq3573 eq5329
    | (have j0 := eq5329 X0 X1
       grind)
    | exact resolve eq5329 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329
  have eq5359 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5346 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5346
    | (have j0 := eq5346 X0 X1
       grind)
    | exact resolve eq5346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5346
  have eq5368 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5359 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5359
    | (have j0 := eq5359 X0 X1
       grind)
    | exact resolve eq5359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5359
  have eq26259 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq5368 X1 X0
       grind)
    | exact superpose eq5368 eq11
    | (have j1 := eq5368 X1 X0
       grind)
    | exact resolve eq11 eq5368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5368
  have eq26372 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26259 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq26259
    | (have j0 := eq26259 X0 X1
       grind)
    | exact resolve eq26259 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq26259
  have eq26728 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq26372 (σ X1) X0
       grind)
    | exact superpose eq26372 eq15
    | (have j1 := eq26372 (σ X1) X0
       grind)
    | exact resolve eq15 eq26372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26372
  have eq44963 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26728 x y
       grind)
    | exact superpose eq26728 eq16
    | (have j1 := eq26728 x y
       grind)
    | exact resolve eq16 eq26728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26728
  have eq45324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44963
       have i₂ := eq439 y x
       grind)
    | exact superpose eq439 eq44963
    | (have j1 := eq439 x x
       grind)
    | (have r₁ := eq44963
       have r₂ := eq439 y x
       grind)
    | exact resolve eq44963 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq44963
  have eq45325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq45324
  have eq45326 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq45325
  have eq45555 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19 y x X0
       have i₂ := eq45326
       grind)
    | exact superpose eq45326 eq19
    | exact resolve eq19 eq45326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45326
  have eq46207 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq45555 (M.op x x)
       have i₂ := eq45555 x
       grind)
    | exact superpose eq45555 eq45555
    | exact resolve eq45555 eq45555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45555
  have eq46253 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq46207
  have eq46741 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3843 x (σ y)
       have i₂ := eq46253
       grind)
    | exact superpose eq46253 eq3843
    | exact resolve eq3843 eq46253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843
  have eq46746 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 (σ y) (σ x) X0
       have i₂ := eq46253
       grind)
    | exact superpose eq46253 eq19
    | exact resolve eq19 eq46253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq46253
  have eq48163 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq46746 (σ (M.op x x))
       have i₂ := eq46741
       grind)
    | exact superpose eq46741 eq46746
    | exact resolve eq46746 eq46741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46741 eq46746
  have eq48226 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq48163
  have eq48235 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq48226
       have i₂ := eq3573 x
       grind)
    | exact superpose eq3573 eq48226
    | exact resolve eq48226 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48226
  have eq48252 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3477 x
       have i₂ := eq48235
       grind)
    | exact superpose eq48235 eq3477
    | (have j0 := eq3477 x
       grind)
    | (have r₁ := eq3477 x
       have r₂ := eq48235
       grind)
    | exact resolve eq3477 eq48235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48267 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq3833 x x
       have i₂ := eq48235
       grind)
    | exact superpose eq48235 eq3833
    | (have r₁ := eq3833 x x
       have r₂ := eq48235
       grind)
    | exact resolve eq3833 eq48235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833 eq48235
  have eq48326 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq48267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48267
  have eq48333 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq48252
  have eq48342 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq48326 X0
       have j1 := eq3478 x X0
       grind)
    | (have r₁ := eq48326 X0
       have r₂ := eq3478 x x
       grind)
    | exact resolve eq48326 eq3478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3478 eq48326
  have eq48348 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq3477 x
       grind)
    | (have r₁ := eq48333
       have r₂ := eq3477 x
       grind)
    | exact resolve eq48333 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477 eq48333
  have eq48356 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq48348
       have i₂ := eq3573 x
       grind)
    | exact superpose eq3573 eq48348
    | exact resolve eq48348 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3573 eq48348
  have eq48715 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq48356
       grind)
    | exact superpose eq48356 eq10
    | exact resolve eq10 eq48356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48356
  have eq48944 : x = (M.op x x) := by
    first
    | (have i₁ := eq48715
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48715
    | exact resolve eq48715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48715
  have eq49002 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq34 x x
       have i₂ := eq48944
       grind)
    | exact superpose eq48944 eq34
    | (have r₁ := eq34 x x
       have r₂ := eq48944
       grind)
    | exact resolve eq34 eq48944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq48944
  have eq49097 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq49002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49002
  have eq50663 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq48342 (σ X0)
       grind)
    | exact superpose eq48342 eq15
    | exact resolve eq15 eq48342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48342
  have eq50773 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq50663 X0
       have i₂ := eq49097 X0
       grind)
    | exact superpose eq49097 eq50663
    | exact resolve eq50663 eq49097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49097 eq50663
  have eq53029 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq50773 y
       grind)
    | exact superpose eq50773 eq16
    | (have r₁ := eq16
       have r₂ := eq50773 y
       grind)
    | exact resolve eq16 eq50773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50773
  have eq53175 : False := by grind
  exact eq53175

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq31 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq35 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq35 X0 X1
       grind)
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq41
  have eq124 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq44 X1 X0
       grind)
    | (have r₁ := eq124 X1 X0
       have r₂ := eq44 X0 X1
       grind)
    | (have r₁ := eq124 X1 X1
       have r₂ := eq44 X1 X1
       grind)
    | exact resolve eq124 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq124
  have eq251 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq128 (σ X1) (σ X0)
       grind)
    | exact superpose eq128 eq15
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 X1
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq251
    | exact resolve eq251 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq251
  have eq261 : False := by grind
  exact eq261

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
    | (have r₁ := eq11 (M.op (M.op X1 X1) (M.op X1 X1)) X1
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
  clear eq38
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
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
  clear eq48
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq51
    | (have j0 := eq51 x
       grind)
    | exact resolve eq51 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (k (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq13 eq182
    | (have j0 := eq182 X0 X1 X2
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq182 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq184 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq177 X0 X0 X0
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq13 eq195
    | (have j0 := eq195 X0 X1
       have j1 := eq13 X0 X0
       grind)
    | exact resolve eq195 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq197 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq184 eq177
    | exact resolve eq177 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq188 eq177
    | exact resolve eq177 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq28 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X0 X1)) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 (M.op (k X0 X1) X2)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 x
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (σ x) = (M.op (k X0 (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 X0
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq189
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq790 : ∀ X0 X1 : G, x = (k (M.op (M.op X0 X1) x) (M.op x y)) ∨ (M.op (M.op X0 X1) x) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq28 (M.op (M.op X0 X1) x) sF0
       grind)
    | exact superpose eq28 eq179
    | (have j1 := eq28 (M.op (M.op X0 X1) x) (M.op x y)
       grind)
    | exact resolve eq179 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq798 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq764 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq764 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq811 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq41
    | exact resolve eq41 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq811
    | exact resolve eq811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq814 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq812
    | exact resolve eq812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq816 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X1 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq28 X0 X0
       grind)
    | (have r₁ := eq12 (k X1 X1) X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq819
    | (have j0 := eq819 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq823 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq816 X0 X1
       have j1 := eq808 X0
       grind)
    | (have r₁ := eq816 X0 (M.op (k X0 X0) (k X0 X0))
       have r₂ := eq808 (k X0 X0)
       grind)
    | (have r₁ := eq816 X0 X1
       have r₂ := eq808 X0
       grind)
    | (have r₁ := eq816 X0 X0
       have r₂ := eq808 X0
       grind)
    | exact resolve eq816 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq829 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq808 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq808
    | (have j0 := eq808 (σ X0)
       grind)
    | exact resolve eq808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq803
    | exact resolve eq803 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq832
       have r₂ := eq27
       grind)
    | exact resolve eq832 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq843 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq839
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq839
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq839 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq839 eq12
    | (have j0 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq839
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq839
       grind)
    | exact resolve eq12 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq839 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq839 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq839 eq177
    | exact resolve eq177 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq839 eq177
    | exact resolve eq177 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq839 eq191
    | exact resolve eq191 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq858 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq849 eq843
    | exact resolve eq843 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq892 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq839 eq850
    | exact resolve eq850 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq908 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq892
  have eq910 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq908
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq908
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq908 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq908 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq849 eq116
    | exact resolve eq116 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq992
    | exact resolve eq992 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1008 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq916 eq98
    | exact resolve eq98 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq1008
    | exact resolve eq1008 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1024 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq858 eq116
    | exact resolve eq116 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1031 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq1024
    | exact resolve eq1024 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1113 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1031 eq855
    | exact resolve eq855 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq1031
  have eq1127 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k y y) := by grind
  clear eq1113
  have eq1133 : x = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1127
    | exact resolve eq1127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1185 : (τ (σ y)) = (k x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq910 eq98
    | exact resolve eq98 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1185
    | exact resolve eq1185 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq809 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 (σ X0) X1
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : y = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq820 y
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq820
    | (have j0 := eq820 y
       grind)
    | exact resolve eq820 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1212 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq910 eq820
    | (have j0 := eq820 (σ x)
       grind)
    | exact resolve eq820 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq1216 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq849 eq820
    | (have j0 := eq820 (σ y)
       grind)
    | exact resolve eq820 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1227 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq1212
  have eq1237 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq1216
    | exact resolve eq1216 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1241 : y = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1211
       have r₂ := eq12 y y
       grind)
    | (have r₁ := eq1211
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1211 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1253 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq839 eq1237
    | exact resolve eq1237 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1254 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1253
  have eq1264 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq1254
       grind)
    | exact superpose eq1254 eq177
    | exact resolve eq177 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1303 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1241
       grind)
    | exact superpose eq1241 eq36
    | exact resolve eq36 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1241
  have eq1306 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1303
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1303
    | exact resolve eq1303 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1313 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1264 y
       have i₂ := eq1254
       grind)
    | exact superpose eq1254 eq1264
    | exact resolve eq1264 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1329 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1313
  have eq1423 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1306 eq803
    | exact resolve eq803 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq1430 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq839 eq1423
    | exact resolve eq1423 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq1423
  have eq1487 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1430 eq177
    | exact resolve eq177 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1650 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq858 eq823
    | (have j0 := eq823 (σ y) X0
       grind)
    | (have r₁ := eq823 (σ y) (σ x)
       have r₂ := eq858
       grind)
    | exact resolve eq823 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq858
  have eq1654 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq845 eq1650
    | (have j0 := eq1650 X0
       have j1 := eq845 X0
       grind)
    | (have r₁ := eq1650 (σ y)
       have r₂ := eq845 X0
       grind)
    | (have r₁ := eq1650 X0
       have r₂ := eq845 (M.op (σ x) (σ x))
       grind)
    | exact resolve eq1650 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1655 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1654 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1837 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1194 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1194
       grind)
    | exact resolve eq13 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1850 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq1837 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq2013 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1227 eq108
    | exact resolve eq108 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1227
  have eq2016 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq2013
    | exact resolve eq2013 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2053 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2016 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq2016
       grind)
    | exact resolve eq13 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2068 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq2053 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053
  have eq2151 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq845 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq2157 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2151 eq91
    | exact resolve eq91 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq2151
  have eq2162 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq2157
    | exact resolve eq2157 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2165 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq798 eq2162
    | exact resolve eq2162 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq2162
  have eq2170 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq2165
       grind)
    | exact superpose eq2165 eq184
    | exact resolve eq184 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2170 eq188
    | exact resolve eq188 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5904 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq1850 eq1194
    | exact resolve eq1194 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq1850
  have eq5938 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by grind
  clear eq5904
  have eq6109 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq5938 eq142
    | exact resolve eq142 eq5938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5938
  have eq6140 : y = (k x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq6109
    | exact resolve eq6109 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6109
  have eq6151 : x ≠ y ∨ x = (M.op y y) ∨ x = (k x x) := by grind
  have eq6468 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2068 eq2016
    | exact resolve eq2016 eq2068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016 eq2068
  have eq6502 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq6468
  have eq6616 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq6502 eq142
    | exact resolve eq142 eq6502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6502
  have eq6649 : x = (k y x) ∨ x = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq6616
    | exact resolve eq6616 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6616
  have eq7347 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq1655 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655
  have eq7348 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq7347
    | exact resolve eq7347 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7347
  have eq7379 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq7348 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq7348
       grind)
    | exact resolve eq13 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7348
  have eq7397 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq7379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7379
  have eq8170 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7397 eq908
    | exact resolve eq908 eq7397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq8214 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8170
  have eq8264 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq916 eq8214
    | exact resolve eq8214 eq916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8214
  have eq8403 : (τ (σ y)) = (k x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8264 eq98
    | exact resolve eq98 eq8264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8264
  have eq8459 : y = (k x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32 eq8403
    | exact resolve eq8403 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8403
  have eq11663 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq767 x x X0
       have i₂ := eq6140
       grind)
    | exact superpose eq6140 eq767
    | (have j0 := eq767 x x x
       grind)
    | exact resolve eq767 eq6140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq11820 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq11663 X0
       have j1 := eq808 x
       grind)
    | (have r₁ := eq11663 X0
       have r₂ := eq808 x
       grind)
    | exact resolve eq11663 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11663
  have eq11908 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq768 x x X0
       have i₂ := eq6140
       grind)
    | exact superpose eq6140 eq768
    | (have j0 := eq768 x x x
       grind)
    | exact resolve eq768 eq6140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6140
  have eq12274 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq11908 X0
       have j1 := eq808 x
       grind)
    | (have r₁ := eq11908 X0
       have r₂ := eq808 x
       grind)
    | exact resolve eq11908 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11908
  have eq17637 : y = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq184 (M.op x x)
       have i₂ := eq12274 x
       grind)
    | exact superpose eq12274 eq184
    | exact resolve eq184 eq12274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17755 : x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17637 eq11820
    | exact resolve eq11820 eq17637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11820 eq17637
  have eq17787 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq17755
  have eq17807 : y = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq184
    | exact resolve eq184 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17825 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq177
    | exact resolve eq177 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17827 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq178 y y x
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq178
    | exact resolve eq178 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq17854 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17807 eq188
    | exact resolve eq188 eq17807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17807
  have eq17927 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17854 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq17854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18009 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17825 y
       have i₂ := eq17787
       grind)
    | exact superpose eq17787 eq17825
    | exact resolve eq17825 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17825
  have eq18058 : y = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq18009
  have eq18120 : x ≠ y ∨ x = (M.op x x) := by grind
  clear eq18058
  have eq19560 : (M.op x y) = (M.op y y) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17927 eq197
    | exact resolve eq197 eq17927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19914 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq196
    | (have j0 := eq196 X0 X1
       have j1 := eq28 X1 (k X0 X0)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq196 (M.op X1 X1) X1
       have r₂ := eq28 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq196 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19987 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq19914 X0 X1
       have j1 := eq196 X0 X1
       grind)
    | (have r₁ := eq19914 X0 X1
       have r₂ := eq196 X0 X1
       grind)
    | exact resolve eq19914 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq19914
  have eq20066 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ y = (M.op x x) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq769 y x x
       have i₂ := eq6649
       grind)
    | exact superpose eq6649 eq769
    | (have j0 := eq769 y x x
       grind)
    | exact resolve eq769 eq6649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6649
  have eq20122 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1306 eq769
    | (have j0 := eq769 (σ x) (σ y) x
       grind)
    | exact resolve eq769 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq20325 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq851 eq20122
    | (have j0 := eq20122 X0
       have j1 := eq851 X0
       grind)
    | exact resolve eq20122 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851 eq20122
  have eq20336 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = y ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq12274 eq20066
    | (have j0 := eq20066 X0
       have j1 := eq12274 X0
       grind)
    | exact resolve eq20066 eq12274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12274 eq20066
  have eq20364 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq20336 X0
       grind)
    | (have r₁ := eq20336 X0
       have r₂ := eq6151
       grind)
    | exact resolve eq20336 eq6151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6151 eq20336
  have eq20404 : x = (M.op x y) ∨ x = (M.op x x) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq17787
       have i₂ := eq19560
       grind)
    | exact superpose eq19560 eq17787
    | exact resolve eq17787 eq19560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19560
  have eq20456 : x = (k y (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20404
  have eq23535 : x = (k x x) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq20364 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20364
    | (have j0 := eq20364 y
       grind)
    | exact resolve eq20364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23570 : ∀ X1 : G, x ≠ (M.op x x) ∨ (k X1 (k x x)) = (M.op X1 (k x x)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X1
    first
    | (have i₁ := eq183 y (M.op x x) x
       have i₂ := eq20364 x
       grind)
    | exact superpose eq20364 eq183
    | exact resolve eq183 eq20364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq20364
  have eq23629 : ∀ X1 : G, (k X1 (k x x)) = (M.op X1 (k x x)) ∨ x = (k x x) ∨ x = (M.op y y) := by
    intro X1
    first
    | (have j0 := eq23570 X1
       grind)
    | (have r₁ := eq23570 X1
       have r₂ := eq17787
       grind)
    | exact resolve eq23570 eq17787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17787 eq23570
  have eq23631 : ∀ X1 : G, (k X1 (k x x)) = (M.op X1 (k x x)) ∨ x = (M.op y y) := by
    intro X1
    first
    | (have j0 := eq23629 X1
       have j1 := eq19987 x X1
       grind)
    | (have r₁ := eq23629 X1
       have r₂ := eq19987 x X1
       grind)
    | exact resolve eq23629 eq19987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19987 eq23629
  have eq23665 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq23535
       grind)
    | exact superpose eq23535 eq40
    | exact resolve eq40 eq23535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23677 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq829 x
       have i₂ := eq23535
       grind)
    | exact superpose eq23535 eq829
    | (have j0 := eq829 x
       grind)
    | exact resolve eq829 eq23535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq23535
  have eq23687 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq23677
  have eq23715 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23687
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23687
    | exact resolve eq23687 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23687
  have eq23717 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq23665
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23665
    | exact resolve eq23665 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23665
  have eq23728 : (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq908 eq23715
    | exact resolve eq23715 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq23715
  have eq23733 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2195 eq23728
    | exact resolve eq23728 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq23728
  have eq23743 : (M.op x y) = (M.op x x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23733 eq207
    | exact resolve eq207 eq23733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23733
  have eq23806 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17827 x
       have i₂ := eq23743
       grind)
    | exact superpose eq23743 eq17827
    | (have j0 := eq17827 y
       grind)
    | exact resolve eq17827 eq23743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17827 eq23743
  have eq23854 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq23806
  have eq23871 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23854 eq184
    | exact resolve eq184 eq23854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23854
  have eq24395 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23717 eq916
    | exact resolve eq916 eq23717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916 eq23717
  have eq24469 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq24395
  have eq24497 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2165 eq24469
    | exact resolve eq24469 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24469
  have eq24538 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq24497 eq177
    | exact resolve eq177 eq24497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24497
  have eq25281 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23631 x
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq23631
    | exact resolve eq23631 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25292 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq23631 x
       have i₂ := eq8459
       grind)
    | exact superpose eq8459 eq23631
    | exact resolve eq23631 eq8459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8459
  have eq25358 : y = (M.op (M.op x y) (k y (k x x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq184 (k x x)
       have i₂ := eq23631 y
       grind)
    | exact superpose eq23631 eq184
    | exact resolve eq184 eq23631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23631
  have eq25417 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq25292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25292
  have eq25421 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq25281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25281
  have eq25452 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2165 eq25421
    | exact resolve eq25421 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25421
  have eq25469 : y = (M.op (M.op x y) (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25358
       have i₂ := eq1014
       grind)
    | exact superpose eq1014 eq25358
    | exact resolve eq25358 eq1014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014 eq25358
  have eq25527 : y = (M.op (M.op x y) (k y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq25469
  have eq25533 : y = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq998 eq25527
    | exact resolve eq25527 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25527
  have eq25536 : y = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2170 eq25533
    | exact resolve eq25533 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq25533
  have eq25538 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23871 eq25536
    | exact resolve eq25536 eq23871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23871 eq25536
  have eq25614 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25538 eq24538
    | exact resolve eq24538 eq25538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24538 eq25538
  have eq25650 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) := by grind
  clear eq25614
  have eq25662 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2165 eq25650
    | exact resolve eq25650 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25650
  have eq25663 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq25662
  have eq25804 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25663 eq207
    | exact resolve eq207 eq25663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25663
  have eq25896 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25804 eq197
    | exact resolve eq197 eq25804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25804
  have eq25947 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2165 eq25896
    | exact resolve eq25896 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165 eq25896
  have eq28170 : x ≠ (k y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq25417
  have eq28235 : x ≠ x ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28170
       have i₂ := eq998
       grind)
    | exact superpose eq998 eq28170
    | (have r₁ := eq28170
       have r₂ := eq998
       grind)
    | exact resolve eq28170 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq28236 : x ≠ x ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28170
       have i₂ := eq1133
       grind)
    | exact superpose eq1133 eq28170
    | (have r₁ := eq28170
       have r₂ := eq1133
       grind)
    | exact resolve eq28170 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq28170
  have eq28266 : x ≠ x ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28236
  have eq28267 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28266
  have eq28268 : x ≠ x ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq28235
  have eq28269 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq28268
  have eq28310 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq28267
       grind)
    | exact superpose eq28267 eq177
    | exact resolve eq177 eq28267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28267
  have eq29034 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28310 y
       have i₂ := eq28269
       grind)
    | exact superpose eq28269 eq28310
    | exact resolve eq28310 eq28269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28269 eq28310
  have eq29096 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq29034
  have eq29109 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1329 eq29096
    | exact resolve eq29096 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq29096
  have eq29110 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq29109
  have eq29224 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq29110
       grind)
    | exact superpose eq29110 eq188
    | exact resolve eq188 eq29110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29242 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x x
       have i₂ := eq29110
       grind)
    | exact superpose eq29110 eq177
    | exact resolve eq177 eq29110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29110
  have eq29301 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29224 eq184
    | exact resolve eq184 eq29224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29224
  have eq30686 : x = (k (M.op y x) (M.op x y)) ∨ y = (M.op y x) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17927 eq790
    | exact resolve eq790 eq17927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq17927
  have eq30805 : (M.op x y) = (k (M.op y (M.op x y)) (M.op x y)) ∨ y = (M.op y x) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20456 eq30686
    | exact resolve eq30686 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30686
  have eq30810 : (M.op x y) = (k (M.op y (M.op x y)) (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20456 eq30805
    | exact resolve eq30805 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30805
  have eq30814 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17854 eq30810
    | exact resolve eq30810 eq17854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30810
  have eq30818 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20456 eq30814
    | exact resolve eq30814 eq20456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20456 eq30814
  have eq30822 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq17854 eq30818
    | exact resolve eq30818 eq17854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17854 eq30818
  have eq30826 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq30822
       have r₂ := eq18120
       grind)
    | exact resolve eq30822 eq18120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18120 eq30822
  have eq32638 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29301 eq29242
    | exact resolve eq29242 eq29301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29242 eq29301
  have eq32695 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32638
  have eq32774 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq32695
       grind)
    | exact superpose eq32695 eq28
    | exact resolve eq28 eq32695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32695
  have eq39522 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq32774
       grind)
    | exact superpose eq32774 eq41
    | exact resolve eq41 eq32774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32774
  have eq39553 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39522
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39522
    | exact resolve eq39522 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39522
  have eq39559 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39553
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39553
    | exact resolve eq39553 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39553
  have eq39587 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39559 eq768
    | (have j0 := eq768 (σ y) (σ y) x
       grind)
    | exact resolve eq768 eq39559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39559
  have eq39595 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1487 eq39587
    | (have j0 := eq39587 X0
       have j1 := eq1487 X0
       grind)
    | exact resolve eq39587 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487 eq39587
  have eq39596 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq39595 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39595
  have eq39603 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20325 eq39596
    | (have j0 := eq39596 X0
       have j1 := eq20325 X0
       grind)
    | exact resolve eq39596 eq20325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20325 eq39596
  have eq39604 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq39603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39603
  have eq44160 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25452 eq25947
    | exact resolve eq25947 eq25452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25452 eq25947
  have eq44208 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq44160
  have eq46620 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq44208 eq1197
    | (have j0 := eq1197 (M.op x y) X0
       grind)
    | exact resolve eq1197 eq44208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq44208
  have eq46627 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq46620 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46620
  have eq46638 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq46627
    | (have j0 := eq46627 X0
       grind)
    | exact resolve eq46627 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46627
  have eq46645 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1254 eq46638
    | exact resolve eq46638 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254 eq46638
  have eq46651 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq46645 X0
       have j1 := eq846 X0
       grind)
    | (have r₁ := eq46645 X0
       have r₂ := eq846 X0
       grind)
    | exact resolve eq46645 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq46645
  have eq48132 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq46651 eq26
    | (have j1 := eq46651 (σ x)
       grind)
    | exact resolve eq26 eq46651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46651
  have eq48211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq48132
    | exact resolve eq48132 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq48132
  have eq48269 : x = (M.op y y) := by
    first
    | (have r₁ := eq48211
       have r₂ := eq27
       grind)
    | exact resolve eq48211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48211
  have eq48318 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq48269
       grind)
    | exact superpose eq48269 eq184
    | exact resolve eq184 eq48269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq48356 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq48269
       grind)
    | exact superpose eq48269 eq28
    | exact resolve eq28 eq48269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48357 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq48269
       grind)
    | exact superpose eq48269 eq177
    | exact resolve eq177 eq48269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48399 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq48318 eq188
    | exact resolve eq188 eq48318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48420 : (M.op x y) = (M.op x x) ∨ y = (k (M.op x y) x) := by
    first
    | exact superpose eq48318 eq28
    | (have j0 := eq28 (M.op x y) x
       grind)
    | exact resolve eq28 eq48318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48318
  have eq48485 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq48399 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq48399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48598 : y = (M.op x x) := by
    first
    | (have i₁ := eq48357 y
       have i₂ := eq48269
       grind)
    | exact superpose eq48269 eq48357
    | exact resolve eq48357 eq48269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48357
  have eq48746 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq48598
       grind)
    | exact superpose eq48598 eq28
    | exact resolve eq28 eq48598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48761 : ∀ X0 : G, x = (M.op (k X0 x) y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq768 X0 x x
       have i₂ := eq48598
       grind)
    | exact superpose eq48598 eq768
    | exact resolve eq768 eq48598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49261 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq48356
       grind)
    | exact superpose eq48356 eq41
    | exact resolve eq41 eq48356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq49271 : y = (k x y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq820 y
       have i₂ := eq48356
       grind)
    | exact superpose eq48356 eq820
    | (have j0 := eq820 y
       grind)
    | exact resolve eq820 eq48356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48356
  have eq49293 : x = y ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq49271
       have i₂ := eq48269
       grind)
    | exact superpose eq48269 eq49271
    | exact resolve eq49271 eq48269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49271
  have eq49294 : y = (k x y) ∨ x = y := by grind
  clear eq49293
  have eq49295 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49261
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq49261
    | exact resolve eq49261 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49261
  have eq49301 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49295
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49295
    | exact resolve eq49295 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49295
  have eq49340 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq49301 eq768
    | (have j0 := eq768 (σ y) (σ y) x
       grind)
    | exact resolve eq768 eq49301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49301
  have eq49342 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq39604 eq49340
    | (have j0 := eq49340 X0
       have j1 := eq39604 X0
       grind)
    | exact resolve eq49340 eq39604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39604 eq49340
  have eq49369 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq48746
       grind)
    | exact superpose eq48746 eq40
    | exact resolve eq40 eq48746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49415 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq49369
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49369
    | exact resolve eq49369 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49369
  have eq49422 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq49415
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq49415
    | exact resolve eq49415 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49415
  have eq50205 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq49422 eq779
    | (have j0 := eq779 (σ x)
       grind)
    | exact resolve eq779 eq49422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq49422
  have eq50590 : y = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq48598
       have i₂ := eq48420
       grind)
    | exact superpose eq48420 eq48598
    | exact resolve eq48598 eq48420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50613 : y = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq48420
       grind)
    | exact superpose eq48420 eq188
    | exact resolve eq188 eq48420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq48420
  have eq50686 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50590 eq40
    | exact resolve eq40 eq50590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50711 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq50686
    | exact resolve eq50686 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50686
  have eq50713 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50711
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50711
    | exact resolve eq50711 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50711
  have eq50736 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq50713 eq769
    | (have j0 := eq769 (σ (M.op x y)) (σ x) x
       grind)
    | exact resolve eq769 eq50713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50713
  have eq50751 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k y (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq48485
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq48485
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq48485 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50762 : (M.op x y) = (M.op y y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq48485 eq197
    | exact resolve eq197 eq48485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50769 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq48485 eq28
    | exact resolve eq28 eq48485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48485
  have eq50810 : x = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50762
       have i₂ := eq48269
       grind)
    | exact superpose eq48269 eq50762
    | exact resolve eq50762 eq48269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48269 eq50762
  have eq70314 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30826 eq50769
    | exact resolve eq50769 eq30826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30826 eq50769
  have eq70339 : y = (M.op x y) ∨ x = (k y (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq70314
  have eq70356 : x = y ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | (have i₁ := eq70339
       have i₂ := eq48598
       grind)
    | exact superpose eq48598 eq70339
    | exact resolve eq70339 eq48598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70339
  have eq70374 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq50810 eq70356
    | exact resolve eq70356 eq50810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50810 eq70356
  have eq70375 : x = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq70374
  have eq82209 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq50205 eq49342
    | exact resolve eq49342 eq50205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49342 eq50205
  have eq82329 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq82209
  have eq83863 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (k y (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq50751 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq50751
       grind)
    | exact resolve eq13 eq50751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50751
  have eq83918 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (k y (M.op x y)) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq83863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83863
  have eq83955 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (k y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq70375 eq83918
    | (have j0 := eq83918 X0
       grind)
    | exact resolve eq83918 eq70375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70375 eq83918
  have eq83969 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = (k y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq83955 X0
       have j1 := eq809 (M.op x y) X0
       grind)
    | (have r₁ := eq83955 X0
       have r₂ := eq809 (M.op x y) x
       grind)
    | exact resolve eq83955 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq83955
  have eq84192 : x = (k y (M.op x y)) ∨ x = (k y (M.op x y)) := by
    first
    | exact superpose eq83969 eq48399
    | exact resolve eq48399 eq83969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83969
  have eq84287 : x = (k y (M.op x y)) := by grind
  clear eq84192
  have eq84416 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq84287 eq42
    | exact resolve eq42 eq84287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq84422 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq84416
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq84416
    | exact resolve eq84416 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84416
  have eq84424 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq84422
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84422
    | exact resolve eq84422 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84422
  have eq84432 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq84424 eq769
    | (have j0 := eq769 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq769 eq84424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq84433 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq84424 eq768
    | (have j0 := eq768 (σ y) (σ (M.op x y)) x
       grind)
    | exact resolve eq768 eq84424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq85035 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq84433 eq84432
    | exact resolve eq84432 eq84433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84432 eq84433
  have eq85091 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq85035
  have eq85099 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq85091 eq28
    | exact resolve eq28 eq85091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq85100 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq85091 eq177
    | exact resolve eq177 eq85091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86100 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq85091 eq85100
    | exact resolve eq85100 eq85091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85100
  have eq86188 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq86100
  have eq87470 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq85099 eq820
    | (have j0 := eq820 (σ (M.op x y))
       grind)
    | exact resolve eq820 eq85099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq85099
  have eq87482 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq84424 eq87470
    | exact resolve eq87470 eq84424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84424 eq87470
  have eq87487 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq85091 eq87482
    | exact resolve eq87482 eq85091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85091 eq87482
  have eq87488 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq87487
  have eq87510 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq87488 eq177
    | exact resolve eq177 eq87488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq87488
  have eq92006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50736 eq87510
    | exact resolve eq87510 eq50736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50736 eq87510
  have eq92077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq92006
    | exact resolve eq92006 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92006
  have eq92083 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq92077
       have r₂ := eq27
       grind)
    | exact resolve eq92077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92077
  have eq92681 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq92083 eq82329
    | exact resolve eq82329 eq92083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82329 eq92083
  have eq92819 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq92681
  have eq92863 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq92819 eq29
    | exact resolve eq29 eq92819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92819
  have eq93018 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq92863
    | exact resolve eq92863 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq92863
  have eq93019 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq93018
  have eq93052 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93019 eq29
    | exact resolve eq29 eq93019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq93019
  have eq93196 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq93052
    | exact resolve eq93052 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq93052
  have eq93213 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq93196
       grind)
    | exact superpose eq93196 eq18
    | exact resolve eq18 eq93196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93505 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq48399
       have i₂ := eq93196
       grind)
    | exact superpose eq93196 eq48399
    | exact resolve eq48399 eq93196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48399
  have eq94002 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93213 eq197
    | exact resolve eq197 eq93213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq93213
  have eq94098 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93196 eq94002
    | exact resolve eq94002 eq93196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93196 eq94002
  have eq94559 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq94098 eq93505
    | exact resolve eq93505 eq94098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93505 eq94098
  have eq94655 : x = (M.op x y) ∨ x = y := by grind
  clear eq94559
  have eq94677 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq94655
       grind)
    | exact superpose eq94655 eq18
    | exact resolve eq18 eq94655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94678 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq94655
       grind)
    | exact superpose eq94655 eq22
    | exact resolve eq22 eq94655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95144 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq94678
    | exact resolve eq94678 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94678
  have eq95170 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) ∨ x = y := by
    first
    | exact superpose eq95144 eq132
    | exact resolve eq132 eq95144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq95171 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq95144 eq133
    | exact resolve eq133 eq95144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq95144
  have eq95261 : (k x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq99 eq95171
    | exact resolve eq95171 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq95171
  have eq95262 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq98 eq95170
    | exact resolve eq95170 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq95170
  have eq95291 : y = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq49294 eq95261
    | exact resolve eq95261 eq49294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49294 eq95261
  have eq95292 : y = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq48746 eq95262
    | exact resolve eq95262 eq48746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48746 eq95262
  have eq95295 : y = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50590 eq95292
    | exact resolve eq95292 eq50590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50590 eq95292
  have eq95297 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94655 eq95295
    | exact resolve eq95295 eq94655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95295
  have eq95314 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq94677 eq207
    | exact resolve eq207 eq94677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq94677
  have eq95417 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq94655 eq95314
    | exact resolve eq95314 eq94655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94655 eq95314
  have eq95739 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq95297 eq48761
    | (have j0 := eq48761 (M.op x y)
       grind)
    | exact resolve eq48761 eq95297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48761 eq95297
  have eq95768 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95739
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95739
    | exact resolve eq95739 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq95739
  have eq95769 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq95768
  have eq96123 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84287
       have i₂ := eq95769
       grind)
    | exact superpose eq95769 eq84287
    | exact resolve eq84287 eq95769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84287
  have eq96125 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95291
       have i₂ := eq95769
       grind)
    | exact superpose eq95769 eq95291
    | exact resolve eq95291 eq95769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95291 eq95769
  have eq96126 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq96125
  have eq96211 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96126 eq96123
    | exact resolve eq96123 eq96126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96123 eq96126
  have eq96212 : x = (M.op x y) := by grind
  clear eq96211
  have eq96402 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq96212
       grind)
    | exact superpose eq96212 eq22
    | exact resolve eq22 eq96212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq96727 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq48598
       have i₂ := eq96212
       grind)
    | exact superpose eq96212 eq48598
    | exact resolve eq48598 eq96212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48598
  have eq96736 : y = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50613
       have i₂ := eq96212
       grind)
    | exact superpose eq96212 eq50613
    | exact resolve eq50613 eq96212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50613
  have eq96768 : x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq95417 eq96736
    | exact resolve eq96736 eq95417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95417 eq96736
  have eq96897 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq96768
       have i₂ := eq96212
       grind)
    | exact superpose eq96212 eq96768
    | exact resolve eq96768 eq96212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96212 eq96768
  have eq96912 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq808 (M.op x y)
       grind)
    | (have r₁ := eq96897
       have r₂ := eq808 (M.op x y)
       grind)
    | exact resolve eq96897 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq96897
  have eq96916 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq96402 eq20
    | exact resolve eq20 eq96402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97499 : y = (M.op x y) := by
    first
    | exact superpose eq96912 eq96727
    | exact resolve eq96727 eq96912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96727 eq96912
  have eq97803 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq97499
       grind)
    | exact superpose eq97499 eq24
    | exact resolve eq24 eq97499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq97499
  have eq98266 : (σ x) = (σ y) := by
    first
    | exact superpose eq96402 eq97803
    | exact resolve eq97803 eq96402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96402 eq97803
  have eq98382 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98266 eq26
    | exact resolve eq26 eq98266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq98582 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98266 eq86188
    | exact resolve eq86188 eq98266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86188 eq98266
  have eq98626 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq96916 eq98582
    | exact resolve eq98582 eq96916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98582
  have eq98734 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq98382 eq98626
    | exact resolve eq98626 eq98382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98626
  have eq98783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq98382 eq98734
    | exact resolve eq98734 eq98382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98382 eq98734
  have eq98810 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq98783
       have r₂ := eq27
       grind)
    | exact resolve eq98783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98783
  have eq98822 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq98810 eq27
    | exact resolve eq27 eq98810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq98810
  have eq98922 : False := by grind
  exact eq98922

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq108 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1039 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1056 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq1047
    | (have j0 := eq1047 X0 X1
       grind)
    | exact resolve eq1047 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1047
  have eq1064 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq1039
    | (have j0 := eq1039 X0 X1
       grind)
    | exact resolve eq1039 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1078 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq1064
    | (have j0 := eq1064 X0 X1
       grind)
    | exact resolve eq1064 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq2885 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1078 x y
       grind)
    | exact superpose eq1078 eq16
    | (have j1 := eq1078 x y
       grind)
    | exact resolve eq16 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq5906 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1056 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1056
    | (have j0 := eq1056 X1 (σ X0)
       grind)
    | exact resolve eq1056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq5983 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5906 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5906
    | (have j0 := eq5906 X0 X1
       grind)
    | exact resolve eq5906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5906
  have eq5995 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5983 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq5983
    | (have j0 := eq5983 X0 X1
       grind)
    | exact resolve eq5983 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5983
  have eq6002 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5995 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5995
    | (have j0 := eq5995 X0 X1
       grind)
    | exact resolve eq5995 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5995
  have eq7225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2885
       have i₂ := eq6002 y x
       grind)
    | exact superpose eq6002 eq2885
    | (have j1 := eq6002 x y
       grind)
    | (have r₁ := eq2885
       have r₂ := eq6002 y x
       grind)
    | (have r₁ := eq2885
       have r₂ := eq6002 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2885
       have r₂ := eq6002 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2885 eq6002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885 eq6002
  have eq7226 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq7225
  have eq12918 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7226
       grind)
    | exact superpose eq7226 eq16
    | exact resolve eq16 eq7226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7226
  have eq12919 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq12918
       have r₂ := eq22 x
       grind)
    | exact resolve eq12918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12918
  have eq12924 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq12919
       grind)
    | exact superpose eq12919 eq22
    | exact resolve eq22 eq12919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12919
  have eq12989 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12924
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq12924
    | exact resolve eq12924 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12924
  have eq12990 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq12989
  have eq13021 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq12990
       grind)
    | exact superpose eq12990 eq10
    | exact resolve eq10 eq12990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12990
  have eq13128 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq13021
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq13021
    | exact resolve eq13021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13021
  have eq13129 : (M.op x x) = (M.op y y) := by grind
  clear eq13128
  have eq13205 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq108 X0 y y
       have i₂ := eq13129
       grind)
    | exact superpose eq13129 eq108
    | exact resolve eq108 eq13129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13222 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq13205 y
       have i₂ := eq13129
       grind)
    | exact superpose eq13129 eq13205
    | exact resolve eq13205 eq13129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13129 eq13205
  have eq13245 : x = y := by
    first
    | (have i₁ := eq13222
       have i₂ := eq108 x x x
       grind)
    | (have i₁ := eq13222
       have i₂ := eq108 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq108 eq13222
    | exact resolve eq13222 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq13222
  have eq13246 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13245
       grind)
    | exact superpose eq13245 eq16
    | exact resolve eq16 eq13245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13245
  have eq13248 : False := by grind
  exact eq13248

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pxy_pxx_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq65 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq47
    | exact resolve eq47 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (M.op x y) X0
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq84 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq27 eq69
    | (have j0 := eq69 (M.op x y)
       grind)
    | exact resolve eq69 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq90 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq116 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (k X0 X1)) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (k X0 X1)) = X0 ∨ (M.op X0 X1) = (k X1 X1) ∨ X0 = X1 := by
    intro X0 X1 X2 X3
    grind
  clear eq116
  have eq165 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    grind
  have eq168 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq43 eq49
    | exact resolve eq49 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq43 eq49
    | exact resolve eq49 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq183 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq188 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    grind
  clear eq183
  have eq206 : (τ (σ y)) = (M.op (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by grind
  clear eq168
  have eq274 : ∀ X1 : G, (M.op x y) = (M.op (τ (σ x)) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq49
    | exact resolve eq49 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq175
  have eq326 : (M.op x y) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) := by grind
  clear eq274
  have eq336 : (M.op x y) ≠ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq326 eq13
    | (have j0 := eq13 (τ (σ x)) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq341 : (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) := by grind
  clear eq336
  have eq342 : (M.op x y) = (k (τ (σ x)) (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq341
       have r₂ := eq188 (M.op x y)
       grind)
    | exact resolve eq341 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq368 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq65
    | exact resolve eq65 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq860 : (τ (σ y)) ≠ (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq206 eq90
    | (have j0 := eq90 (M.op x y) (k (τ (σ y)) (τ (σ y)))
       grind)
    | exact resolve eq90 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq206
  have eq863 : (τ (σ y)) = (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have r₁ := eq860
       have r₂ := eq188 (τ (σ y))
       grind)
    | exact resolve eq860 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq1070 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq1071 : (σ (M.op x y)) = (k (σ (τ (σ x))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1070
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1070
    | exact resolve eq1070 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1073 : (σ (M.op x y)) = (k (σ (τ (σ x))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq1071
    | exact resolve eq1071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1074 : (σ (M.op x y)) = (k (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1073
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1073
    | exact resolve eq1073 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1234 : ∀ X0 X3 : G, (k X0 X3) = (M.op X0 (k (k X0 X3) (k X0 X3))) ∨ (M.op X0 X3) = (k X3 X3) ∨ X0 = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq55 (k X0 X3) (M.op x x) X0
       have i₂ := eq122 X0 X3 x x
       grind)
    | exact superpose eq122 eq55
    | (have j1 := eq122 X0 X3 x X3
       grind)
    | exact resolve eq55 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq122
  have eq1753 : (σ (τ (σ y))) = (k (σ (M.op x y)) (σ (k (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq863 eq15
    | exact resolve eq15 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1757 : (σ (τ (σ y))) = (k (σ (M.op x y)) (k (σ (τ (σ y))) (σ (τ (σ y))))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq1753
       have i₂ := eq15 (τ sF5) (τ sF5)
       grind)
    | exact superpose eq15 eq1753
    | exact resolve eq1753 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1761 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq1757
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1757
    | exact resolve eq1757 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1762 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq27 eq1761
    | exact resolve eq1761 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761
  have eq8539 : (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op (σ (M.op x y)) (k (σ y) (σ y))) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq1762 eq1234
    | (have j0 := eq1234 (σ (M.op x y)) (k (σ y) (σ y))
       grind)
    | exact resolve eq1234 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq8542 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1074 eq1234
    | (have j0 := eq1234 (σ x) (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq1234 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1234
  have eq8656 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8542
       have i₂ := eq188 sF3
       grind)
    | exact superpose eq188 eq8542
    | exact resolve eq8542 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8542
  have eq8657 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by grind
  clear eq8656
  have eq8660 : (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq8539
       have i₂ := eq188 sF5
       grind)
    | exact superpose eq188 eq8539
    | exact resolve eq8539 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8539
  have eq8661 : (σ y) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq8660
  have eq10604 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq8657 eq53
    | exact resolve eq53 eq8657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq15327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq8661 eq10604
    | exact resolve eq10604 eq8661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10604
  have eq15352 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq8661 eq165
    | exact resolve eq165 eq8661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq8661
  have eq15390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq33 eq15327
    | exact resolve eq15327 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15327
  have eq15391 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq15390
       have r₂ := eq34
       grind)
    | exact resolve eq15390 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15390
  have eq1114538 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15391 eq188
    | exact resolve eq188 eq15391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15391
  have eq1114547 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1114538 eq36
    | exact resolve eq36 eq1114538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114538
  have eq1114548 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1114547
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1114547
    | exact resolve eq1114547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114547
  have eq1114550 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq1114548
    | exact resolve eq1114548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114548
  have eq1114554 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1114550 eq36
    | exact resolve eq36 eq1114550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114550
  have eq1114555 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1114554
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1114554
    | exact resolve eq1114554 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114554
  have eq1114557 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq1114555
    | exact resolve eq1114555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114555
  have eq1114558 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq1114557
  have eq1114594 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1114558 eq188
    | exact resolve eq188 eq1114558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114558
  have eq1114619 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq1114594
  have eq1114665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1114619 eq15352
    | exact resolve eq15352 eq1114619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15352
  have eq1114921 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1114619 eq188
    | exact resolve eq188 eq1114619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114619
  have eq1115396 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq1114665
  have eq1115455 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq33 eq1115396
    | exact resolve eq1115396 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115396
  have eq1115473 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq1115455
       have r₂ := eq34
       grind)
    | exact resolve eq1115455 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115455
  have eq1115482 : (k (M.op x y) (M.op x y)) = (τ (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1114921 eq84
    | exact resolve eq84 eq1114921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1115523 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1114921
  have eq1115529 : (k (M.op x y) (M.op x y)) = (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1115482
       have i₂ := eq368 (k sF5 sF5) (k sF5 sF5)
       grind)
    | exact superpose eq368 eq1115482
    | exact resolve eq1115482 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115482
  have eq1115537 : (k (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1115529
       have i₂ := eq368 sF5 sF5
       grind)
    | exact superpose eq368 eq1115529
    | exact resolve eq1115529 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq1115529
  have eq1115543 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1115537
       have i₂ := eq188 (τ sF5)
       grind)
    | exact superpose eq188 eq1115537
    | exact resolve eq1115537 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115537
  have eq1115655 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1115543 eq36
    | exact resolve eq36 eq1115543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115543
  have eq1115664 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1115655
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1115655
    | exact resolve eq1115655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115655
  have eq1115668 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1115664
    | exact resolve eq1115664 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115664
  have eq1115713 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1115668 eq8657
    | exact resolve eq8657 eq1115668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8657 eq1115668
  have eq1116481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33 eq1115713
    | exact resolve eq1115713 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115713
  have eq1116497 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq1116481
       have r₂ := eq34
       grind)
    | exact resolve eq1116481 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116481
  have eq1119256 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1115473 eq15
    | exact resolve eq15 eq1115473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115473
  have eq1119263 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1119256
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1119256
    | exact resolve eq1119256 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119256
  have eq1119283 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq1119263
    | exact resolve eq1119263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119263
  have eq1119284 : (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq1119283
  have eq1133210 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1116497 eq36
    | exact resolve eq36 eq1116497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1116497
  have eq1133211 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1133210
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1133210
    | exact resolve eq1133210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133210
  have eq1133215 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1133211
    | exact resolve eq1133211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1133211
  have eq1133216 : (σ x) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1119284 eq1133215
    | exact resolve eq1133215 eq1119284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133215
  have eq1133217 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1133216
       have i₂ := eq188 sF5
       grind)
    | exact superpose eq188 eq1133216
    | exact resolve eq1133216 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133216
  have eq1133218 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1133217
  have eq1133219 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1119284 eq1133218
    | exact resolve eq1133218 eq1119284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119284 eq1133218
  have eq1133321 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1133219 eq188
    | exact resolve eq188 eq1133219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133219
  have eq1133958 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1133321
       have i₂ := eq188 sF4
       grind)
    | exact superpose eq188 eq1133321
    | exact resolve eq1133321 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1133321
  have eq1133959 : (σ x) = (σ y) := by grind
  clear eq1133958
  have eq1133973 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1133959 eq33
    | exact resolve eq33 eq1133959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1134913 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1133959 eq1115523
    | exact resolve eq1115523 eq1133959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115523 eq1133959
  have eq1134929 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1134913
  have eq1135361 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1133973
  have eq1136184 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq1135361 eq34
    | exact resolve eq34 eq1135361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1135361
  have eq1136682 : False := by grind
  exact eq1136682

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq42 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq42 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq42 X2 X0 x
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq42 X3 X0 x
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (σ X0) (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq42
    | exact resolve eq42 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq89 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq131 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) ∨ (M.op (M.op X0 X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq43 X0 X1 X2
       grind)
    | exact superpose eq43 eq13
    | (have j0 := eq13 (M.op (M.op X0 X1) X2) X0
       grind)
    | exact resolve eq13 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq266 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1189 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1238 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1189 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1189
    | (have j0 := eq1189 X0 X1
       grind)
    | exact resolve eq1189 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1360 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 (τ X1) (τ X0)
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq278
    | (have j0 := eq278 (τ X1) (τ X0)
       grind)
    | exact resolve eq278 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1367 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1360 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1360
    | (have j0 := eq1360 X0 X1
       grind)
    | exact resolve eq1360 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1370 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1367 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1367
    | (have j0 := eq1367 X0 X1
       grind)
    | exact resolve eq1367 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1372 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1370 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1370
    | (have j0 := eq1370 X0 X1
       grind)
    | exact resolve eq1370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1373 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1372 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1372
    | (have j0 := eq1372 X0 X1
       grind)
    | exact resolve eq1372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1374 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1373 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1373
    | (have j0 := eq1373 X0 X1
       grind)
    | exact resolve eq1373 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1375 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1374
    | (have j0 := eq1374 X0 X1
       grind)
    | exact resolve eq1374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1662 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq266
       have i₂ := eq1238 y x
       grind)
    | exact superpose eq1238 eq266
    | (have j1 := eq1238 (σ y) (σ x)
       grind)
    | (have r₁ := eq266
       have r₂ := eq1238 y x
       grind)
    | (have r₁ := eq266
       have r₂ := eq1238 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq266
       have r₂ := eq1238 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq266 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq1238
  have eq1663 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1662
  have eq10052 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1663
       grind)
    | exact superpose eq1663 eq16
    | exact resolve eq16 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663
  have eq10053 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10052
       have r₂ := eq22 x
       grind)
    | exact resolve eq10052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10052
  have eq10234 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq42 X0 x y
       have i₂ := eq10053
       grind)
    | exact superpose eq10053 eq42
    | exact resolve eq42 eq10053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10235 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq42 x y X0
       have i₂ := eq10053
       grind)
    | exact superpose eq10053 eq42
    | exact resolve eq42 eq10053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10053
  have eq10252 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10234 (M.op x x)
       have i₂ := eq10234 x
       grind)
    | exact superpose eq10234 eq10234
    | exact resolve eq10234 eq10234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10234
  have eq10279 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq10252
  have eq10459 : (σ x) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq56 x (σ y)
       have i₂ := eq10279
       grind)
    | exact superpose eq10279 eq56
    | exact resolve eq56 eq10279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq10466 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq42 X0 (σ x) (σ y)
       have i₂ := eq10279
       grind)
    | exact superpose eq10279 eq42
    | exact resolve eq42 eq10279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq10279
  have eq11386 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10466 (σ (M.op x x))
       have i₂ := eq10459
       grind)
    | exact superpose eq10459 eq10466
    | exact resolve eq10466 eq10459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10459 eq10466
  have eq11421 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq11386
  have eq11427 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11421
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11421
    | exact resolve eq11421 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11421
  have eq11469 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ x = (M.op (M.op (M.op X0 X1) x) x) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 x X1 x x
       have i₂ := eq11427
       grind)
    | exact superpose eq11427 eq50
    | exact resolve eq50 eq11427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11427
  have eq16458 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq11469 X0 X1
       grind)
    | exact superpose eq11469 eq10
    | (have j1 := eq11469 X0 X1
       grind)
    | exact resolve eq10 eq11469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11469
  have eq16570 : ∀ X0 X1 : G, x = y ∨ x = (M.op (M.op (M.op X0 X1) x) x) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq16458 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16458
    | (have j0 := eq16458 X0 X1
       grind)
    | exact resolve eq16458 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16458
  have eq16706 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq16570 X0 X1
       grind)
    | exact superpose eq16570 eq16
    | (have j1 := eq16570 X0 X1
       grind)
    | exact resolve eq16 eq16570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16570
  have eq16707 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq16706 X0 X1
       grind)
    | (have r₁ := eq16706 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq16706 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16706
  have eq16729 : ∀ X0 X1 : G, (M.op x x) = (τ (σ x)) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq16707 X0 X1
       grind)
    | exact superpose eq16707 eq10
    | (have j1 := eq16707 X0 X1
       grind)
    | exact resolve eq10 eq16707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16707
  have eq16858 : ∀ X0 X1 : G, x = (M.op x x) ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16729 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16729
    | (have j0 := eq16729 X0 X1
       grind)
    | exact resolve eq16729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16729
  have eq17023 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) x) ∨ x = (M.op (M.op (M.op X1 X2) x) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq48 x X1 x
       have i₂ := eq16858 X0 X1
       grind)
    | exact superpose eq16858 eq48
    | (have j1 := eq16858 X1 X2
       grind)
    | exact resolve eq48 eq16858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq16858
  have eq17228 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq17023 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17023
  have eq17229 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) x) := by
    intro X0 X1
    first
    | (have j0 := eq17228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17228
  have eq17323 : x = (M.op x x) := by
    first
    | (have i₁ := eq17229 (M.op x x) x
       have i₂ := eq17229 x x
       grind)
    | exact superpose eq17229 eq17229
    | exact resolve eq17229 eq17229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17229
  have eq17572 : ∀ X0 : G, x ≠ x ∨ x = (k (M.op x X0) x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq131 x x x
       have i₂ := eq17323
       grind)
    | exact superpose eq17323 eq131
    | (have r₁ := eq131 x x x
       have r₂ := eq17323
       grind)
    | exact resolve eq131 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq17579 : ∀ X0 : G, x = (k (M.op x X0) x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq17572 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17572
  have eq18497 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17579 (M.op y x)
       have i₂ := eq10235 x
       grind)
    | exact superpose eq10235 eq17579
    | exact resolve eq17579 eq10235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10235 eq17579
  have eq33785 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18497
       grind)
    | exact superpose eq18497 eq16
    | exact resolve eq16 eq18497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18497
  have eq33786 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq33785
       have r₂ := eq22 x
       grind)
    | exact resolve eq33785 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33785
  have eq33800 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq33786
       grind)
    | exact superpose eq33786 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq33786
       grind)
    | exact resolve eq13 eq33786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33786
  have eq33820 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq33800
  have eq33821 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq33820
  have eq33825 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq33821
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq33821
    | exact resolve eq33821 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33821
  have eq33830 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq33825
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq33825
    | exact resolve eq33825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33825
  have eq33832 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq33830
       have i₂ := eq17323
       grind)
    | exact superpose eq17323 eq33830
    | exact resolve eq33830 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33830
  have eq34046 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq278 x y
       have i₂ := eq33832
       grind)
    | exact superpose eq33832 eq278
    | (have j0 := eq278 x y
       grind)
    | (have r₁ := eq278 x y
       have r₂ := eq33832
       grind)
    | exact resolve eq278 eq33832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33832
  have eq34086 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq34046
  have eq34087 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq34086
  have eq34100 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq278 x y
       grind)
    | (have r₁ := eq34087
       have r₂ := eq278 x y
       grind)
    | exact resolve eq34087 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq34087
  have eq34404 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34100
       grind)
    | exact superpose eq34100 eq16
    | exact resolve eq16 eq34100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34416 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq34100
       grind)
    | exact superpose eq34100 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq34100
       grind)
    | exact resolve eq13 eq34100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34100
  have eq34436 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq34416
  have eq34437 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq34436
  have eq34441 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34437
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq34437
    | exact resolve eq34437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34437
  have eq34446 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34441
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq34441
    | exact resolve eq34441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34441
  have eq34448 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq34446
       have i₂ := eq17323
       grind)
    | exact superpose eq17323 eq34446
    | exact resolve eq34446 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34446
  have eq34649 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq34448
       grind)
    | exact superpose eq34448 eq10
    | exact resolve eq10 eq34448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34448
  have eq34767 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq34649
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34649
    | exact resolve eq34649 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34649
  have eq34771 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34767
       grind)
    | exact superpose eq34767 eq16
    | exact resolve eq16 eq34767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34767
  have eq34772 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq34771
       have r₂ := eq22 x
       grind)
    | exact resolve eq34771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34771
  have eq35092 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq34772
       grind)
    | exact superpose eq34772 eq10
    | exact resolve eq10 eq34772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34772
  have eq35214 : x = (k y x) := by
    first
    | (have i₁ := eq35092
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq35092
    | exact resolve eq35092 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35092
  have eq35239 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1375 y x
       have i₂ := eq35214
       grind)
    | exact superpose eq35214 eq1375
    | (have j0 := eq1375 y x
       grind)
    | (have r₁ := eq1375 y x
       have r₂ := eq35214
       grind)
    | exact resolve eq1375 eq35214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375 eq35214
  have eq35269 : x = y ∨ x = (M.op x y) := by grind
  clear eq35239
  have eq35471 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35269
       grind)
    | exact superpose eq35269 eq16
    | exact resolve eq16 eq35269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35269
  have eq35476 : x = (M.op x y) := by
    first
    | (have r₁ := eq35471
       have r₂ := eq22 x
       grind)
    | exact resolve eq35471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35471
  have eq35482 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34404
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq34404
    | exact resolve eq34404 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34404
  have eq35515 : (σ x) = (σ y) := by grind
  clear eq35482
  have eq35817 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35515
       grind)
    | exact superpose eq35515 eq16
    | exact resolve eq16 eq35515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35515
  have eq35937 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq35817
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq35817
    | exact resolve eq35817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35817
  have eq35939 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq35937
       have i₂ := eq17323
       grind)
    | exact superpose eq17323 eq35937
    | exact resolve eq35937 eq17323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323 eq35937
  have eq35941 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq35939
       have i₂ := eq35476
       grind)
    | exact superpose eq35476 eq35939
    | exact resolve eq35939 eq35476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35476 eq35939
  have eq35942 : False := by grind
  exact eq35942

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pxx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq29 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36
    | (have j0 := eq36 x
       grind)
    | exact resolve eq36 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36
    | (have j0 := eq36 y
       grind)
    | exact resolve eq36 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq110 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq99
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq149 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq132
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq149
  have eq166 : (σ (k (k (M.op x y) (M.op x y)) x)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq132 eq39
    | exact resolve eq39 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq192 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq207 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq210 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq16
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq305 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq361 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq458 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x X0 X1 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq234 eq53
    | exact resolve eq53 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq538 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq239 eq53
    | exact resolve eq53 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq542 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq544 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq548 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq551 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq681 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq942 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) (τ X0)) = (τ (k (k (σ (M.op x y)) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq132 eq361
    | exact resolve eq361 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq1295 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq458 (M.op x X0) (M.op (M.op (M.op x x) x) X0)
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq458
    | exact resolve eq458 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq458
  have eq1617 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq481 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq481
    | exact resolve eq481 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481
  have eq1839 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq490 X1 X0
       grind)
    | exact superpose eq490 eq14
    | exact resolve eq14 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2582 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq542 (M.op sF0 X0) X0
       have i₂ := eq14 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq14 eq542
    | exact resolve eq542 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq2768 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq544 (M.op sF4 X0) X0
       have i₂ := eq14 X0 sF4 (M.op sF4 X0)
       grind)
    | exact superpose eq14 eq544
    | exact resolve eq544 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq2816 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq534 eq548
    | exact resolve eq548 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq548
  have eq2846 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2816 X0
       have i₂ := eq490 y (M.op x X0)
       grind)
    | exact superpose eq490 eq2816
    | exact resolve eq2816 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq2902 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq538 eq551
    | exact resolve eq551 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538 eq551
  have eq2930 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2902 X0
       have i₂ := eq490 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq490 eq2902
    | exact resolve eq2902 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq2902
  have eq5379 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq210 eq2582
    | exact resolve eq2582 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq2582
  have eq5441 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq5379
       have i₂ := eq1839 x x
       grind)
    | exact superpose eq1839 eq5379
    | exact resolve eq5379 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5379
  have eq5764 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq219 eq2768
    | exact resolve eq2768 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq2768
  have eq5828 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5764
       have i₂ := eq1839 sF2 sF2
       grind)
    | exact superpose eq1839 eq5764
    | exact resolve eq5764 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5764
  have eq6137 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2846 eq520
    | exact resolve eq520 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq6142 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2930 eq520
    | exact resolve eq520 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq2930
  have eq7262 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq681
    | exact resolve eq681 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq681
  have eq7385 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7262 X0 X1
       have i₂ := eq1839 X0 X0
       grind)
    | exact superpose eq1839 eq7262
    | exact resolve eq7262 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7262
  have eq7521 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5441 eq7385
    | exact resolve eq7385 eq5441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5441
  have eq7570 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq236 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq7385 (M.op x X0) y
       grind)
    | exact superpose eq7385 eq236
    | exact resolve eq236 eq7385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq7572 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq241 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq7385 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq7385 eq241
    | exact resolve eq241 eq7385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq7385
  have eq7905 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7570 (M.op x (M.op X0 x))
       have i₂ := eq1617 x X0
       grind)
    | exact superpose eq1617 eq7570
    | exact resolve eq7570 eq1617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7570
  have eq8263 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7572 (M.op sF2 (M.op x sF2))
       have i₂ := eq1617 sF2 x
       grind)
    | exact superpose eq1617 eq7572
    | exact resolve eq7572 eq1617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617 eq7572
  have eq14817 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq170 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq170
    | (have j0 := eq170 x
       grind)
    | exact resolve eq170 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq14888 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14817
  have eq14893 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14888
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq14888
    | exact resolve eq14888 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14888
  have eq14900 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq14893
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq14893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14893
  have eq14906 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq14900 eq49
    | exact resolve eq49 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq14964 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq15023 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq14964
  have eq15027 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15023
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq15023
    | exact resolve eq15023 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15023
  have eq15036 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq15027
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq15027 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15027
  have eq15043 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq15036 eq87
    | exact resolve eq87 eq15036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq15102 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq207
    | (have j0 := eq207 (M.op x y)
       grind)
    | exact resolve eq207 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq15154 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq15102
  have eq15156 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq132 eq15154
    | exact resolve eq15154 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15154
  have eq15167 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq15156
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq15156 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15156
  have eq15175 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq15167 eq155
    | exact resolve eq155 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq46445 : (σ (k (k (M.op x y) (M.op x y)) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq15167 eq166
    | exact resolve eq166 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq50577 : (k (k (M.op x y) (M.op x y)) x) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x))) := by
    first
    | exact superpose eq46445 eq16
    | exact resolve eq16 eq46445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46445
  have eq53490 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15036 eq109
    | exact resolve eq109 eq15036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq53829 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14900 eq110
    | exact resolve eq110 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq54311 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15167 eq156
    | exact resolve eq156 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq59247 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) (τ X0)) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq15167 eq942
    | exact resolve eq942 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq70523 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq53490
       grind)
    | exact superpose eq53490 eq16
    | exact resolve eq16 eq53490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53490
  have eq70596 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq15043 eq70523
    | exact resolve eq70523 eq15043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15043 eq70523
  have eq70599 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq70596
       have r₂ := eq13 y y
       grind)
    | exact resolve eq70596 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70596
  have eq70602 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53829
       grind)
    | exact superpose eq53829 eq16
    | exact resolve eq16 eq53829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53829
  have eq70675 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq14906 eq70602
    | exact resolve eq70602 eq14906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70602
  have eq70678 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq70675
       have r₂ := eq13 x x
       grind)
    | exact resolve eq70675 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70675
  have eq70679 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70599
       grind)
    | exact superpose eq70599 eq76
    | exact resolve eq76 eq70599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq70599
  have eq70718 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15036 eq70679
    | exact resolve eq70679 eq15036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15036 eq70679
  have eq70733 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq43
    | exact resolve eq43 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70772 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq14900 eq70733
    | exact resolve eq70733 eq14900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14900 eq70733
  have eq71644 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq54311 eq16
    | exact resolve eq16 eq54311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54311
  have eq71723 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15175 eq71644
    | exact resolve eq71644 eq15175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71644
  have eq71726 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq71723
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq71723 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71723
  have eq71727 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq71726 eq132
    | exact resolve eq132 eq71726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq71766 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq15167 eq71727
    | exact resolve eq71727 eq15167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15167 eq71727
  have eq73848 : ∀ X0 : G, (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) = (k (M.op (M.op x y) (M.op x y)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq71726 eq59247
    | exact resolve eq59247 eq71726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59247
  have eq79295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq79295
    | exact resolve eq79295 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79295
  have eq79316 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq79305
       have r₂ := eq27
       grind)
    | exact resolve eq79305 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79305
  have eq79345 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq79316 eq8263
    | exact resolve eq8263 eq79316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79347 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq79316 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq79316
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq79316
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq79316
       grind)
    | exact resolve eq13 eq79316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79316
  have eq79454 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq79347
  have eq79457 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6142 eq79345
    | exact resolve eq79345 eq6142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79345
  have eq82817 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq79454 eq114
    | exact resolve eq114 eq79454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq79454
  have eq82835 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq82817
  have eq83241 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq82835 eq14906
    | exact resolve eq14906 eq82835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82835
  have eq83456 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83241
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq83241
    | exact resolve eq83241 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83241
  have eq83465 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28 eq83456
    | exact resolve eq83456 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83456
  have eq83466 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq83465
  have eq83491 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq83466 eq79457
    | exact resolve eq79457 eq83466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79457 eq83466
  have eq83617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq83491
  have eq83623 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq83617
       have r₂ := eq27
       grind)
    | exact resolve eq83617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83617
  have eq84643 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq83623 eq14906
    | exact resolve eq14906 eq83623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83623
  have eq84858 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq84643
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq84643
    | exact resolve eq84643 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84643
  have eq84867 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq84858
    | exact resolve eq84858 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84858
  have eq84868 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq84867
  have eq85255 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1295 y
       have i₂ := eq84868
       grind)
    | exact superpose eq84868 eq1295
    | exact resolve eq1295 eq84868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq85261 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7905 y
       have i₂ := eq84868
       grind)
    | exact superpose eq84868 eq7905
    | exact resolve eq7905 eq84868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84868
  have eq85373 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6137 eq85261
    | exact resolve eq85261 eq6137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85261
  have eq85378 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85255
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85255
    | exact resolve eq85255 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq85255
  have eq85402 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70718
       have i₂ := eq85373
       grind)
    | exact superpose eq85373 eq70718
    | exact resolve eq70718 eq85373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85373
  have eq85541 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq85402
    | exact resolve eq85402 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85402
  have eq85571 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq85378 eq71766
    | exact resolve eq71766 eq85378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71766
  have eq85573 : ∀ X0 : G, (k y (τ X0)) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq85378 eq73848
    | exact resolve eq73848 eq85378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73848 eq85378
  have eq85717 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq85573 X0
       have i₂ := eq282 X0
       grind)
    | exact superpose eq282 eq85573
    | exact resolve eq85573 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq85573
  have eq85719 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85571
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85571
    | exact resolve eq85571 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq85571
  have eq86271 : (τ (k (σ y) (σ x))) = (k (k (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq85719 eq50577
    | exact resolve eq50577 eq85719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50577 eq85719
  have eq86396 : (τ (k (σ y) (σ x))) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq71726 eq86271
    | exact resolve eq86271 eq71726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86271
  have eq86405 : (k y x) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq82 eq86396
    | exact resolve eq86396 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq86396
  have eq131450 : (k y x) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq86405 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq86405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86405
  have eq131460 : (k y x) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op (M.op (M.op x y) (M.op x y)) x) := by grind
  clear eq131450
  have eq131473 : x = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq7521 eq131460
    | exact resolve eq131460 eq7521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521 eq131460
  have eq153651 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq85717 eq305
    | exact resolve eq305 eq85717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85717
  have eq153768 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) X0) = (τ (k (σ y) (σ X0))) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq15175 eq153651
    | exact resolve eq153651 eq15175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15175 eq153651
  have eq153782 : ∀ X0 : G, (k (k (M.op x y) (M.op x y)) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq153768 x
       have i₂ := eq305 sF3 x
       grind)
    | exact superpose eq305 eq153768
    | exact resolve eq153768 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq153768
  have eq153795 : ∀ X0 : G, (k y X0) = (k (k (M.op x y) (M.op x y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq153782
    | exact resolve eq153782 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq153782
  have eq153803 : ∀ X0 : G, (k y X0) = (k (M.op (M.op x y) (M.op x y)) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq71726 eq153795
    | exact resolve eq153795 eq71726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71726 eq153795
  have eq969255 : x ≠ x ∨ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq131473 eq13
    | (have j0 := eq13 (M.op (M.op x y) (M.op x y)) x
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) (M.op x y)) x
       have r₂ := eq131473
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq131473
       grind)
    | exact resolve eq13 eq131473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131473
  have eq969598 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq969255
  have eq969637 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) x) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq969598
       have i₂ := eq1839 sF0 sF0
       grind)
    | exact superpose eq1839 eq969598
    | exact resolve eq969598 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839 eq969598
  have eq976350 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq969637 eq153803
    | exact resolve eq153803 eq969637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153803 eq969637
  have eq976364 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq976350
  have eq976427 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq976364
       grind)
    | exact superpose eq976364 eq75
    | exact resolve eq75 eq976364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq976364
  have eq976499 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq976427
    | exact resolve eq976427 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976427
  have eq977562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq976499 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq976499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976499
  have eq977587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq977562
    | exact resolve eq977562 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq977562
  have eq977598 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq977587
       have r₂ := eq27
       grind)
    | exact resolve eq977587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977587
  have eq978325 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq977598 eq8263
    | exact resolve eq8263 eq977598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977598
  have eq978740 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq6142 eq978325
    | exact resolve eq978325 eq6142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978325
  have eq979308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq978740 eq85541
    | exact resolve eq85541 eq978740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85541 eq978740
  have eq979867 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq979308
  have eq979905 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq979867
       have r₂ := eq27
       grind)
    | exact resolve eq979867 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979867
  have eq979923 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq979905 eq14906
    | exact resolve eq14906 eq979905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14906 eq979905
  have eq980559 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq979923
       have i₂ := eq70678
       grind)
    | exact superpose eq70678 eq979923
    | exact resolve eq979923 eq70678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70678 eq979923
  have eq980575 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq980559
    | exact resolve eq980559 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq980559
  have eq980576 : x = (M.op x x) := by grind
  clear eq980575
  have eq980586 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70772
       have i₂ := eq980576
       grind)
    | exact superpose eq980576 eq70772
    | exact resolve eq70772 eq980576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70772
  have eq980705 : (M.op x y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq7905 x
       have i₂ := eq980576
       grind)
    | exact superpose eq980576 eq7905
    | exact resolve eq7905 eq980576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7905 eq980576
  have eq981119 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq6137 eq980705
    | exact resolve eq980705 eq6137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6137 eq980705
  have eq981176 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq980586
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq980586
    | exact resolve eq980586 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq980586
  have eq981925 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq70718
       have i₂ := eq981119
       grind)
    | exact superpose eq981119 eq70718
    | exact resolve eq70718 eq981119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70718 eq981119
  have eq982433 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq981925
    | exact resolve eq981925 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq981925
  have eq983007 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq981176 eq5828
    | exact resolve eq5828 eq981176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5828 eq981176
  have eq986045 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq983007 eq8263
    | exact resolve eq8263 eq983007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8263 eq983007
  have eq986459 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6142 eq986045
    | exact resolve eq986045 eq6142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6142 eq986045
  have eq986515 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq982433 eq986459
    | exact resolve eq986459 eq982433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982433 eq986459
  have eq986525 : False := by grind
  exact eq986525
