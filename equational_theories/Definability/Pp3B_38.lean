import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 (M.op x x)) x) X0
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
    | (have i₁ := eq61 X0 (M.op X0 X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq358 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq361 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq359 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq359 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq359 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq372 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq361 (σ X0)
       grind)
    | exact superpose eq361 eq15
    | exact resolve eq15 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq361 X0
       grind)
    | exact superpose eq361 eq372
    | exact resolve eq372 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq372
  have eq441 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq67
    | exact resolve eq67 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq448 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq441 X0 X1
       have j1 := eq444 X0 X1
       grind)
    | (have r₁ := eq441 X0 X1
       have r₂ := eq444 X0 X1
       grind)
    | exact resolve eq441 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq1007 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448
    | exact resolve eq448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq448 X1 (σ X0)
       grind)
    | exact superpose eq448 eq15
    | (have j1 := eq448 X1 (σ X0)
       grind)
    | exact resolve eq15 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq1058 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1007 X1 (τ X0)
       grind)
    | exact superpose eq1007 eq17
    | (have j1 := eq1007 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1007
  have eq1184 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1058 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1058
    | exact resolve eq1058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1184 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1184
    | (have j0 := eq1184 X0 X1
       grind)
    | exact resolve eq1184 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq2053 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1018 x y
       grind)
    | exact superpose eq1018 eq16
    | (have j1 := eq1018 x y
       grind)
    | exact resolve eq16 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq2173 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2053
       have i₂ := eq1250 x y
       grind)
    | exact superpose eq1250 eq2053
    | (have j1 := eq1250 (σ x) (σ y)
       grind)
    | (have r₁ := eq2053
       have r₂ := eq1250 x y
       grind)
    | exact resolve eq2053 eq1250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq2053
  have eq2174 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2173
  have eq2178 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq2174
       grind)
    | exact superpose eq2174 eq61
    | exact resolve eq61 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2185 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2178
       have i₂ := eq2174
       grind)
    | exact superpose eq2174 eq2178
    | exact resolve eq2178 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq2178
  have eq2194 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2185
  have eq2236 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61 (σ x) (σ y)
       have i₂ := eq2194
       grind)
    | exact superpose eq2194 eq61
    | exact resolve eq61 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2300 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2236
       have i₂ := eq2194
       grind)
    | exact superpose eq2194 eq2236
    | exact resolve eq2236 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194 eq2236
  have eq2311 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2300
  have eq2317 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2311
       have i₂ := eq391 y
       grind)
    | exact superpose eq391 eq2311
    | exact resolve eq2311 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311
  have eq2327 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq444 y X0
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq444
    | (have j0 := eq444 y X0
       grind)
    | (have r₁ := eq444 y x
       have r₂ := eq2317
       grind)
    | exact resolve eq444 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2328 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq446 y
       have i₂ := eq2317
       grind)
    | exact superpose eq2317 eq446
    | exact resolve eq446 eq2317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq2317
  have eq2353 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2327
  have eq2361 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2328
       have i₂ := eq391 y
       grind)
    | exact superpose eq391 eq2328
    | exact resolve eq2328 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq2328
  have eq2362 : (σ y) = (σ (M.op y y)) := by grind
  clear eq2361
  have eq2363 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2353 X0
       have j1 := eq444 y X0
       grind)
    | (have r₁ := eq2353 X0
       have r₂ := eq444 y x
       grind)
    | exact resolve eq2353 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq2353
  have eq2379 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq10
    | exact resolve eq10 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2433 : y = (M.op y y) := by
    first
    | (have i₁ := eq2379
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2379
    | exact resolve eq2379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq2450 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2433
       grind)
    | exact superpose eq2433 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2433
       grind)
    | exact resolve eq12 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2486 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2450 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq2579 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2363 (σ X0)
       grind)
    | exact superpose eq2363 eq15
    | exact resolve eq15 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2363
  have eq2599 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2579 X0
       have i₂ := eq2486 X0
       grind)
    | exact superpose eq2486 eq2579
    | exact resolve eq2579 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq2579
  have eq2652 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2599 x
       grind)
    | exact superpose eq2599 eq16
    | (have r₁ := eq16
       have r₂ := eq2599 x
       grind)
    | exact resolve eq16 eq2599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2599
  have eq2693 : False := by grind
  exact eq2693

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyy_pyx_Equation2982 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq83 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83
    | exact resolve eq83 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq10
    | exact resolve eq10 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq108
    | exact resolve eq108 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq299 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq106 (τ X0)
       grind)
    | exact superpose eq106 eq34
    | exact resolve eq34 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq310 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq299 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq299
    | exact resolve eq299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq312 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq310 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq310
    | exact resolve eq310 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq310
  have eq422 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq50 eq54
    | exact resolve eq54 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq423 eq54
    | exact resolve eq54 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq494 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X4 X3)) X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X4 X3)) X4)) X1
       have i₂ := eq52 X3 (M.op X1 X2) X0 X4
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op (M.op X0 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op (M.op sF0 X0) (M.op (M.op X2 (M.op x X0)) x))
       have i₂ := eq52 X0 sF0 X2 x
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq497 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op (M.op X0 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op sF4 X0) (M.op (M.op X2 (M.op x X0)) x))
       have i₂ := eq52 X0 sF4 X2 x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq507 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq424 eq54
    | exact resolve eq54 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq424
  have eq574 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq52 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X1 (M.op X1 X0) x
       have i₂ := eq53 X1 X1 X0 x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq1571 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq422 X0 X1 X2
       have i₂ := eq576 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq422 X0 X1 X2
       have i₂ := eq576 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq576 eq422
    | exact resolve eq422 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq1964 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq574 X0 X1 X2
       have i₂ := eq576 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq574 X0 X1 X2
       have i₂ := eq576 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq576 eq574
    | exact resolve eq574 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq2204 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1964 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1571 X2 X1 X0
       grind)
    | exact superpose eq1571 eq1964
    | exact resolve eq1964 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571 eq1964
  have eq19614 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq496 X0 X1 X0
       have i₂ := eq2204 X0 (M.op sF0 X1) (M.op X0 (M.op X0 X1))
       grind)
    | (have i₁ := eq496 X0 X1 X2
       have i₂ := eq2204 (M.op X0 (M.op X2 X1)) (M.op sF0 X1) X2
       grind)
    | exact superpose eq2204 eq496
    | exact resolve eq496 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq19708 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq497 X0 X1 X0
       have i₂ := eq2204 X0 (M.op sF4 X1) (M.op X0 (M.op X0 X1))
       grind)
    | (have i₁ := eq497 X0 X1 X2
       have i₂ := eq2204 (M.op X0 (M.op X2 X1)) (M.op sF4 X1) X2
       grind)
    | exact superpose eq2204 eq497
    | exact resolve eq497 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq30012 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) X3) (M.op X4 (M.op X0 (M.op X4 X3))))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq494 X0 X1 X2 X3 X4
       have i₂ := eq2204 X4 (M.op (M.op X1 X2) X3) (M.op X0 (M.op X4 X3))
       grind)
    | (have i₁ := eq494 X0 X1 X2 X3 X4
       have i₂ := eq2204 (M.op X0 (M.op X4 X3)) (M.op (M.op X1 X2) X3) X4
       grind)
    | exact superpose eq2204 eq494
    | exact resolve eq494 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq2204
  have eq128745 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq576 (σ X0) sF3
       grind)
    | (have i₁ := eq75 X0
       have i₂ := eq576 sF3 (σ X0)
       grind)
    | exact superpose eq576 eq75
    | (have j0 := eq75 X0
       grind)
    | exact resolve eq75 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq128746 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ y) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq128745 X0
       have i₂ := eq576 (σ X0) sF3
       grind)
    | (have i₁ := eq128745 X0
       have i₂ := eq576 sF3 (σ X0)
       grind)
    | exact superpose eq576 eq128745
    | (have j0 := eq128745 X0
       grind)
    | exact resolve eq128745 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq128745
  have eq128747 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) ∨ (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq128746 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq128746
    | (have j0 := eq128746 X0
       grind)
    | exact resolve eq128746 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128746
  have eq128748 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq128747 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq128747
    | (have j0 := eq128747 X0
       grind)
    | exact resolve eq128747 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq128747
  have eq128757 : ∀ X0 : G, (σ (k y (τ X0))) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq128748 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq128748
    | exact resolve eq128748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128748
  have eq129099 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq128757 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq128757
    | (have j0 := eq128757 X0
       grind)
    | exact resolve eq128757 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq128757
  have eq129140 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq129099 X0
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq129099
    | (have j0 := eq129099 X0
       grind)
    | exact resolve eq129099 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129099
  have eq129158 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq129140 X0
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq129140
    | (have j0 := eq129140 X0
       grind)
    | exact resolve eq129140 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq129140
  have eq129168 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq129158 X0
       have j1 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq129158 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq129158 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129158
  have eq173626 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq129168 eq88
    | (have j1 := eq129168 (σ x)
       grind)
    | exact resolve eq88 eq129168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq173640 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq507 eq173626
    | exact resolve eq173626 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173626
  have eq173678 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq507 eq173640
    | exact resolve eq173640 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173640
  have eq173702 : (k (σ y) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq173678
       grind)
    | exact superpose eq173678 eq70
    | exact resolve eq70 eq173678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173678
  have eq173723 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq173702
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq173702
    | exact resolve eq173702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173702
  have eq175756 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq91 eq129168
    | (have j0 := eq129168 (σ x)
       grind)
    | exact resolve eq129168 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq129168
  have eq175760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq507 eq175756
    | exact resolve eq175756 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175756
  have eq175778 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq175760
       have r₂ := eq27
       grind)
    | exact resolve eq175760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175760
  have eq175784 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq507 eq175778
    | exact resolve eq175778 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507 eq175778
  have eq175936 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq175784 eq30012
    | exact resolve eq30012 eq175784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175784
  have eq176025 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq19708 eq175936
    | exact resolve eq175936 eq19708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175936
  have eq176329 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30012 X0 x x X1 X2
       have i₂ := eq176025
       grind)
    | exact superpose eq176025 eq30012
    | exact resolve eq30012 eq176025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176025
  have eq176418 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19614 eq176329
    | exact resolve eq176329 eq19614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19614 eq176329
  have eq179308 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq176418
       grind)
    | exact superpose eq176418 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq176418
       grind)
    | exact resolve eq13 eq176418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176418
  have eq179472 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq179308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179308
  have eq201223 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq179472 y
       grind)
    | exact superpose eq179472 eq70
    | exact resolve eq70 eq179472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq179472
  have eq201301 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq201223
       have i₂ := eq448
       grind)
    | exact superpose eq448 eq201223
    | exact resolve eq201223 eq448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq201223
  have eq201344 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq201301
    | exact resolve eq201301 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201301
  have eq201371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq201344 eq173723
    | exact resolve eq173723 eq201344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173723 eq201344
  have eq201377 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq201371
       have r₂ := eq27
       grind)
    | exact resolve eq201371 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201371
  have eq201571 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq201377 eq30012
    | exact resolve eq30012 eq201377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30012 eq201377
  have eq201663 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq19708 eq201571
    | exact resolve eq201571 eq19708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19708 eq201571
  have eq201664 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq201663
  have eq201884 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq201664 eq29
    | exact resolve eq29 eq201664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq201664
  have eq202111 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq201884
    | exact resolve eq201884 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq201884
  have eq202112 : x = y := by grind
  clear eq202111
  have eq202421 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq202112
       grind)
    | exact superpose eq202112 eq18
    | exact resolve eq18 eq202112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq202422 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq202112
       grind)
    | exact superpose eq202112 eq24
    | exact resolve eq24 eq202112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq202112
  have eq202636 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq202422
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq202422
    | exact resolve eq202422 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq202422
  have eq202699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq202636 eq26
    | exact resolve eq26 eq202636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq202636
  have eq204175 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq202699 eq112
    | exact resolve eq112 eq202699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq202699
  have eq204563 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq204175
       have i₂ := eq202421
       grind)
    | exact superpose eq202421 eq204175
    | exact resolve eq204175 eq202421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202421 eq204175
  have eq204715 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq204563 eq15
    | exact resolve eq15 eq204563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204563
  have eq204795 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq204715
    | exact resolve eq204715 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq204715
  have eq204816 : False := by grind
  exact eq204816

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxy_pyx_Equation2982 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq36
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq73
    | (have j0 := eq73 (σ X0) (σ X1)
       grind)
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq70
    | (have j1 := eq73 y x
       grind)
    | exact resolve eq70 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq115 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq106 eq73
    | (have j0 := eq73 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq120
    | exact resolve eq120 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq124 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq121
       have r₂ := eq27
       grind)
    | exact resolve eq121 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq126 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq124
    | exact resolve eq124 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq223 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ y)) (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq126 eq51
    | exact resolve eq51 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq232 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq223
    | (have j0 := eq223 (σ x)
       grind)
    | exact resolve eq223 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq223 (M.op sF2 (M.op sF3 X0))
       have i₂ := eq14 X0 sF2 sF3
       grind)
    | exact superpose eq14 eq223
    | exact resolve eq223 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq244 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq126 eq232
    | exact resolve eq232 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq247 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq244
  have eq274 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ x)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq237 eq14
    | exact resolve eq14 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq274 eq247
    | exact resolve eq247 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq274
  have eq292 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq281
  have eq323 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq292 eq237
    | exact resolve eq237 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq292
  have eq326 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq323
  have eq329 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq326
    | exact resolve eq326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq553 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 (M.op X0 X1) x
       have i₂ := eq53 X0 X0 X1 x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq802 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq89 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1189 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq232
       have i₂ := eq553 sF2 (M.op sF4 sF2)
       grind)
    | (have i₁ := eq232
       have i₂ := eq553 (M.op sF4 sF2) sF2
       grind)
    | exact superpose eq553 eq232
    | exact resolve eq232 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1212 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1189
       have i₂ := eq553 sF2 sF4
       grind)
    | (have i₁ := eq1189
       have i₂ := eq553 sF4 sF2
       grind)
    | exact superpose eq553 eq1189
    | exact resolve eq1189 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1319 : (σ y) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1212 eq12
    | (have j0 := eq12 (M.op (σ x) (M.op (σ x) (σ y))) (σ x)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1212
       grind)
    | exact resolve eq12 eq1212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1337 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1319
       have r₂ := eq329
       grind)
    | exact resolve eq1319 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1347 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1337
       have i₂ := eq553 sF2 (M.op sF2 sF4)
       grind)
    | (have i₁ := eq1337
       have i₂ := eq553 (M.op sF2 sF4) sF2
       grind)
    | exact superpose eq553 eq1337
    | exact resolve eq1337 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1350 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (σ x)
       grind)
    | (have r₁ := eq1347
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq1347 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq36274 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq329 eq1350
    | exact resolve eq1350 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq1350
  have eq36278 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq36274
  have eq36282 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq36278
    | exact resolve eq36278 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36278
  have eq36286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq36282 eq106
    | exact resolve eq106 eq36282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq36282
  have eq36290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq36286
  have eq36292 : y = (M.op x y) := by
    first
    | (have r₁ := eq36290
       have r₂ := eq27
       grind)
    | exact resolve eq36290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36290
  have eq36294 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq36292 eq20
    | exact resolve eq20 eq36292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq36298 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op y x) := by
    first
    | exact superpose eq36292 eq115
    | (have r₁ := eq115
       have r₂ := eq36292
       grind)
    | exact resolve eq115 eq36292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq36318 : x = (M.op x x) ∨ (k y x) = (M.op y x) := by grind
  clear eq36298
  have eq36326 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36318
       have i₂ := eq553 x y
       grind)
    | (have i₁ := eq36318
       have i₂ := eq553 y x
       grind)
    | exact superpose eq553 eq36318
    | exact resolve eq36318 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36318
  have eq36330 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36294
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36294
    | exact resolve eq36294 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36294
  have eq36331 : (M.op x y) = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq36326
       have r₂ := eq13 x x
       grind)
    | exact resolve eq36326 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36326
  have eq36333 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq36331
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq36331
    | exact resolve eq36331 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36331
  have eq36334 : y = (k y x) := by
    first
    | exact superpose eq36292 eq36333
    | exact resolve eq36333 eq36292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36292 eq36333
  have eq36449 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq802 x y
       have i₂ := eq36334
       grind)
    | exact superpose eq36334 eq802
    | (have j0 := eq802 x y
       grind)
    | exact resolve eq802 eq36334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802 eq36334
  have eq36452 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36449
  have eq36457 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36452
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36452
    | exact resolve eq36452 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq36452
  have eq36460 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq36457
       have i₂ := eq553 sF3 (σ x)
       grind)
    | (have i₁ := eq36457
       have i₂ := eq553 (σ x) sF3
       grind)
    | exact superpose eq553 eq36457
    | exact resolve eq36457 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36457
  have eq36462 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq36460
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq36460
    | exact resolve eq36460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq36460
  have eq36464 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36462
       have i₂ := eq553 sF2 sF3
       grind)
    | (have i₁ := eq36462
       have i₂ := eq553 sF3 sF2
       grind)
    | exact superpose eq553 eq36462
    | exact resolve eq36462 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq36462
  have eq36465 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq36464
    | exact resolve eq36464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq36464
  have eq36466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36330 eq36465
    | exact resolve eq36465 eq36330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36330 eq36465
  have eq36467 : False := by grind
  exact eq36467

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pyx_Equation2982 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq74 (σ X0)
       grind)
    | exact superpose eq74 eq10
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq74 sF2
       grind)
    | exact superpose eq74 eq50
    | exact resolve eq50 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq79 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq78
       have i₂ := eq74 x
       grind)
    | exact superpose eq74 eq78
    | exact resolve eq78 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq76
    | exact resolve eq76 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq76
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq71
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq228 : ∀ X0 : G, y = (M.op X0 (M.op x (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op x (M.op sF0 X0))
       have i₂ := eq14 X0 x sF0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq391 : y = (M.op (M.op x (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq228 eq228
    | exact resolve eq228 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq394 : y = (M.op (M.op x (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq391
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq391
    | exact resolve eq391 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq442 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq81 X0
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq504 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq394 eq14
    | exact resolve eq14 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq533 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq591 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq533 eq55
    | exact resolve eq55 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq533
  have eq34762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq34763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq34762
    | exact resolve eq34762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34762
  have eq34774 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq34763
       have r₂ := eq28
       grind)
    | exact resolve eq34763 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34763
  have eq34778 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq34774 eq79
    | exact resolve eq79 eq34774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34774
  have eq34892 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq34778
    | exact resolve eq34778 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34778
  have eq34893 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34892
  have eq34923 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq34893
       grind)
    | exact superpose eq34893 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq34893
       grind)
    | exact resolve eq13 eq34893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34924 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq442 x X0
       have i₂ := eq34893
       grind)
    | exact superpose eq34893 eq442
    | (have j0 := eq442 x X0
       grind)
    | exact resolve eq442 eq34893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442 eq34893
  have eq34988 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34924
  have eq34989 : ∀ X0 : G, (k X0 x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq34923 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34923
  have eq35024 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq34988 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34988
    | (have j0 := eq34988 X0
       grind)
    | exact resolve eq34988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34988
  have eq35975 : (k (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq71
       have i₂ := eq34989 y
       grind)
    | exact superpose eq34989 eq71
    | exact resolve eq71 eq34989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq34989
  have eq36023 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq35975
       have i₂ := eq504
       grind)
    | exact superpose eq504 eq35975
    | exact resolve eq35975 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq35975
  have eq36051 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq36023
    | exact resolve eq36023 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36023
  have eq36874 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq35024 eq36051
    | exact resolve eq36051 eq35024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35024 eq36051
  have eq36886 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq36874
  have eq36900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq591 eq36886
    | exact resolve eq36886 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq36886
  have eq36926 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq36900
       have r₂ := eq28
       grind)
    | exact resolve eq36900 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36900
  have eq37130 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq36926 eq30
    | exact resolve eq30 eq36926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36926
  have eq37270 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq37130
    | exact resolve eq37130 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq37130
  have eq37271 : x = y := by grind
  clear eq37270
  have eq37287 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq37271
       grind)
    | exact superpose eq37271 eq19
    | exact resolve eq19 eq37271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq37288 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq37271
       grind)
    | exact superpose eq37271 eq25
    | exact resolve eq25 eq37271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq37271
  have eq37425 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq37288
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37288
    | exact resolve eq37288 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37288
  have eq37442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq37425 eq27
    | exact resolve eq27 eq37425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq37425
  have eq37815 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37442 eq79
    | exact resolve eq79 eq37442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq37442
  have eq37952 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq37815
       have i₂ := eq37287
       grind)
    | exact superpose eq37287 eq37815
    | exact resolve eq37815 eq37287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37287 eq37815
  have eq37984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37952 eq15
    | exact resolve eq15 eq37952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37952
  have eq38027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq37984
    | exact resolve eq37984 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq37984
  have eq38036 : False := by grind
  exact eq38036

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X2) X1) = X0 := by
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
  have eq53 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) x) X0) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 X0)) X3)) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op (M.op X2 (M.op X3 X0)) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X3) X1
       have i₂ := eq14 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 (M.op (M.op X1 X2) X0)) X1
       have i₂ := eq14 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq216 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (σ y) = (M.op (M.op y (σ x)) (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) x)) := by
    first
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq479 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq488 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X1) X1 X0
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X2))) X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X1 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 X2 (M.op X0 (M.op X1 X2)) X0 X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X0 (M.op X0 X1) x
       have i₂ := eq56 X0 X0 X1 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq730 : ∀ X0 : G, x = (M.op X0 (M.op y (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq479 X0
       have i₂ := eq674 y (M.op X0 sF0)
       grind)
    | (have i₁ := eq479 X0
       have i₂ := eq674 (M.op X0 sF0) y
       grind)
    | exact superpose eq674 eq479
    | exact resolve eq479 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq1458 : (σ y) = (M.op (M.op y (σ x)) (M.op x (M.op (M.op (σ x) (σ y)) (M.op x y)))) := by
    first
    | (have i₁ := eq218
       have i₂ := eq674 x (M.op sF4 sF0)
       grind)
    | (have i₁ := eq218
       have i₂ := eq674 (M.op sF4 sF0) x
       grind)
    | exact superpose eq674 eq218
    | exact resolve eq218 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1459 : (σ y) = (M.op (M.op y (σ x)) (M.op x (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq1458
       have i₂ := eq674 sF0 sF4
       grind)
    | (have i₁ := eq1458
       have i₂ := eq674 sF4 sF0
       grind)
    | exact superpose eq674 eq1458
    | exact resolve eq1458 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1921 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq674 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq674 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | exact superpose eq674 eq671
    | exact resolve eq671 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq1923 : (σ x) = (M.op (M.op x (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op y (σ y))) := by
    first
    | exact superpose eq1459 eq57
    | exact resolve eq57 eq1459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1459
  have eq1941 : (σ x) = (M.op (M.op y (σ y)) (M.op x (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq1923
       have i₂ := eq674 (M.op y sF3) (M.op x (M.op sF0 sF4))
       grind)
    | (have i₁ := eq1923
       have i₂ := eq674 (M.op x (M.op sF0 sF4)) (M.op y sF3)
       grind)
    | exact superpose eq674 eq1923
    | exact resolve eq1923 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq2303 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op (M.op (M.op x y) (M.op X0 X1)) x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq216 X0 X1
       have i₂ := eq488 sF0 x (M.op X0 X1)
       grind)
    | (have i₁ := eq216 X0 X1
       have i₂ := eq488 (M.op X0 X1) x sF0
       grind)
    | exact superpose eq488 eq216
    | exact resolve eq216 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq488
  have eq2304 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op x (M.op (M.op x y) (M.op X0 X1)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2303 X0 X1
       have i₂ := eq674 x (M.op sF0 (M.op X0 X1))
       grind)
    | (have i₁ := eq2303 X0 X1
       have i₂ := eq674 (M.op sF0 (M.op X0 X1)) x
       grind)
    | exact superpose eq674 eq2303
    | exact resolve eq2303 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq2303
  have eq31791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq31792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq31791
    | exact resolve eq31791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31791
  have eq31803 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq31792
       have r₂ := eq28
       grind)
    | exact resolve eq31792 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31792
  have eq31807 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq31803
    | exact resolve eq31803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31803
  have eq31846 : (σ y) = (M.op (M.op y (σ y)) (M.op x (M.op (M.op x y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq31807 eq2304
    | exact resolve eq2304 eq31807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2304 eq31807
  have eq31908 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq1941 eq31846
    | exact resolve eq31846 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941 eq31846
  have eq31909 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq31908
  have eq31991 : ∀ X0 : G, y = (M.op X0 (M.op y (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1921 X0 y y
       have i₂ := eq31909
       grind)
    | exact superpose eq31909 eq1921
    | exact resolve eq1921 eq31909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1921 eq31909
  have eq32058 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq730 eq31991
    | exact resolve eq31991 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq31991
  have eq32059 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq32058
  have eq32119 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq32059 eq30
    | exact resolve eq30 eq32059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32059
  have eq32255 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq32119
    | exact resolve eq32119 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32119
  have eq32256 : x = y := by grind
  clear eq32255
  have eq32276 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq32256
       grind)
    | exact superpose eq32256 eq19
    | exact resolve eq19 eq32256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq32277 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq32256
       grind)
    | exact superpose eq32256 eq25
    | exact resolve eq25 eq32256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq32256
  have eq32414 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq32277
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq32277
    | exact resolve eq32277 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq32277
  have eq32433 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32414 eq27
    | exact resolve eq27 eq32414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq32414
  have eq32778 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32433 eq69
    | exact resolve eq69 eq32433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq32433
  have eq32904 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq32778
       have i₂ := eq32276
       grind)
    | exact superpose eq32276 eq32778
    | exact resolve eq32778 eq32276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32276 eq32778
  have eq32939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32904 eq15
    | exact resolve eq15 eq32904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32904
  have eq32981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq32939
    | exact resolve eq32939 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq32939
  have eq32990 : False := by grind
  exact eq32990

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq19 eq33
    | exact resolve eq33 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq35 X1 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 X1) X1))
       have i₂ := eq40 (τ X0) X1
       grind)
    | exact superpose eq40 eq17
    | exact resolve eq17 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op X1 X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq149 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (M.op X1 X1) X1)))
       have i₂ := eq98 (τ X0) X1
       grind)
    | exact superpose eq98 eq17
    | exact resolve eq17 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq154 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq149 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq149
    | exact resolve eq149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq230 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq79
    | exact resolve eq79 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq79
    | (have j0 := eq79 X2 X2
       grind)
    | exact resolve eq79 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq249 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq257 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq259 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq257 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq257 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq257 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq291 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))
       have i₂ := eq154 (τ X0) X1
       grind)
    | exact superpose eq154 eq17
    | exact resolve eq17 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq291 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq291
    | exact resolve eq291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq448 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))
       have i₂ := eq297 (τ X0) X1
       grind)
    | exact superpose eq297 eq17
    | exact resolve eq17 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq448
    | exact resolve eq448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq701 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))
       have i₂ := eq454 (τ X0) X1
       grind)
    | exact superpose eq454 eq17
    | exact resolve eq17 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq701 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq701
    | exact resolve eq701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq730 : ∀ X0 : G, (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ≠ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ∨ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) = (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0
    first
    | (have i₁ := eq250 (σ (σ (σ (M.op (M.op X0 X0) X0))))
       have i₂ := eq154 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X0
       grind)
    | exact superpose eq154 eq250
    | (have j0 := eq250 (σ (σ (σ (M.op (M.op X0 X0) X0))))
       grind)
    | exact resolve eq250 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 : G, (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ≠ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ∨ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) = (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0
    first
    | (have i₁ := eq250 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       have i₂ := eq297 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X0
       grind)
    | exact superpose eq297 eq250
    | (have j0 := eq250 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       grind)
    | exact resolve eq250 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq753 : ∀ X0 : G, (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) = (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0
    first
    | (have j0 := eq732 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq755 : ∀ X0 : G, (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) = (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0
    first
    | (have j0 := eq730 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq845 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ (M.op (M.op X0 X0) X0)) X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq35 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq35 eq259
    | (have j0 := eq259 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq259 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq851 : ∀ X0 X1 : G, (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ≠ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ∨ (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = (k X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X1
       have i₂ := eq154 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X0
       grind)
    | exact superpose eq154 eq259
    | (have j0 := eq259 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X1
       grind)
    | exact resolve eq259 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq853 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ≠ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ∨ (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = (k X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq259 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1
       have i₂ := eq297 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X0
       grind)
    | exact superpose eq297 eq259
    | (have j0 := eq259 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1
       grind)
    | exact resolve eq259 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq876 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = (k X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0 X1
    first
    | (have j0 := eq853 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq878 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = (k X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0 X1
    first
    | (have j0 := eq851 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq884 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq845 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq898 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 X1
       have i₂ := eq454 X1 X0
       grind)
    | exact superpose eq454 eq876
    | exact resolve eq876 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq900 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq878 X0 X1
       have i₂ := eq297 X1 X0
       grind)
    | exact superpose eq297 eq878
    | exact resolve eq878 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq878
  have eq906 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq884
    | exact resolve eq884 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq884
  have eq2231 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       have i₂ := eq900 X0 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       grind)
    | exact superpose eq900 eq454
    | exact resolve eq454 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq2284 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2231 X0 X1
       have i₂ := eq755 X0
       grind)
    | exact superpose eq755 eq2231
    | exact resolve eq2231 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq2231
  have eq2996 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq454 X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))
       have i₂ := eq898 X0 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))
       grind)
    | exact superpose eq898 eq454
    | exact resolve eq454 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq3057 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2996 X0 X1
       have i₂ := eq753 X0
       grind)
    | exact superpose eq753 eq2996
    | exact resolve eq2996 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq2996
  have eq4449 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq233 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) X2
       have i₂ := eq454 (τ X0) X1
       grind)
    | exact superpose eq454 eq233
    | (have j0 := eq233 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) X2
       grind)
    | exact resolve eq233 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq454
  have eq4540 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4449 X0 X1 X2
       have i₂ := eq709 X0 X1
       grind)
    | exact superpose eq709 eq4449
    | (have j0 := eq4449 X0 X1 X2
       grind)
    | exact resolve eq4449 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449
  have eq4577 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4540 X0 X1 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq4540
    | (have j0 := eq4540 X0 X1 X2
       grind)
    | exact resolve eq4540 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4540
  have eq4604 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4577 X0 X1 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq4577 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq4577 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577
  have eq4627 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (M.op (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq4604 X0 x X2
       have i₂ := eq709 X0 x
       grind)
    | exact superpose eq709 eq4604
    | (have j0 := eq4604 X0 x X2
       grind)
    | exact resolve eq4604 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq4604
  have eq5395 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) (k X1 (σ X2))
       have i₂ := eq230 X1 X2 X0
       grind)
    | exact superpose eq230 eq13
    | (have j0 := eq13 (σ X0) (k X1 (σ X2))
       have j1 := eq230 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq230 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (k X0 (σ X1))
       have r₂ := eq230 X0 X1 X2
       grind)
    | exact resolve eq13 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq5414 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5395 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5395
  have eq5415 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq5414 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414
  have eq5416 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ X0) = (σ (k X0 (k (τ X1) X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (k X1 (σ X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5415 X0 X1 X2
       have i₂ := eq28 X1 X2 X0
       grind)
    | exact superpose eq28 eq5415
    | (have j0 := eq5415 X0 X1 X2
       grind)
    | exact resolve eq5415 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5415
  have eq6593 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4627 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4627
    | exact resolve eq4627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6641 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4627 (σ X1) X0
       grind)
    | exact superpose eq4627 eq15
    | (have j1 := eq4627 (σ X1) X0
       grind)
    | exact resolve eq15 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq6752 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq6593 (τ X0) X1
       grind)
    | exact superpose eq6593 eq18
    | (have j1 := eq6593 (τ X0) X1
       grind)
    | exact resolve eq18 eq6593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6593
  have eq12512 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6752 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6752
    | exact resolve eq6752 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6752
  have eq12564 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12512 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq12512
    | (have j0 := eq12512 X0 X1
       grind)
    | exact resolve eq12512 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12512
  have eq26567 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6641 x y
       grind)
    | exact superpose eq6641 eq16
    | (have j1 := eq6641 x y
       grind)
    | exact resolve eq16 eq6641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26681 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq6641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6641
  have eq28052 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26567
       have i₂ := eq12564 x y
       grind)
    | exact superpose eq12564 eq26567
    | (have j1 := eq12564 (σ x) (σ y)
       grind)
    | (have r₁ := eq26567
       have r₂ := eq12564 x y
       grind)
    | exact resolve eq26567 eq12564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26567
  have eq28055 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28052
  have eq28169 : y ≠ y ∨ y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq28055
       grind)
    | exact superpose eq28055 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq28055
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28055
       grind)
    | exact resolve eq13 eq28055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28055
  have eq28205 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28169
  have eq36879 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26681 x y
       have i₂ := eq28205
       grind)
    | exact superpose eq28205 eq26681
    | (have j0 := eq26681 x y
       grind)
    | exact resolve eq26681 eq28205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26681 eq28205
  have eq36888 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq36879
  have eq36889 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq36888
  have eq36907 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36889
       grind)
    | exact superpose eq36889 eq16
    | exact resolve eq16 eq36889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68870 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ X2) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5416 X0 X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))
       have i₂ := eq3057 X0 X1
       grind)
    | exact superpose eq3057 eq5416
    | (have j0 := eq5416 X2 X0 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))
       grind)
    | exact resolve eq5416 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq5416
  have eq69021 : ∀ X0 X1 X2 : G, (σ X2) = (σ (k X2 (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68870 X0 X1 X2
       have i₂ := eq2284 X1 (τ X0)
       grind)
    | exact superpose eq2284 eq68870
    | (have j0 := eq68870 X0 X1 X2
       grind)
    | exact resolve eq68870 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68870
  have eq69060 : ∀ X0 X1 X2 : G, (σ X2) = (k (σ X2) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69021 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq69021
    | (have j0 := eq69021 X0 X1 X2
       grind)
    | exact resolve eq69021 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69021
  have eq69096 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (σ (k X2 (τ X0))) ∨ (σ X2) = (k (σ X2) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq69060 X0 x X2
       have i₂ := eq2284 x (τ X0)
       grind)
    | exact superpose eq2284 eq69060
    | (have j0 := eq69060 X0 x X2
       grind)
    | exact resolve eq69060 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284 eq69060
  have eq69132 : ∀ X0 X2 : G, (k (σ X2) X0) = (M.op X0 (σ X2)) ∨ (σ X2) = (k (σ X2) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq69096 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq69096
    | (have j0 := eq69096 X0 X2
       grind)
    | exact resolve eq69096 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq69096
  have eq69153 : ∀ X0 X2 : G, (k (σ X2) X0) = (M.op X0 (σ X2)) ∨ (σ X2) = (k (σ X2) X0) := by
    intro X0 X2
    first
    | (have j0 := eq69132 X0 X2
       have j1 := eq12 (σ X2) X0
       grind)
    | (have r₁ := eq69132 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq69132 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69132
  have eq69181 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69153 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq69153
    | exact resolve eq69153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69153
  have eq69917 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69181
  have eq70605 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69917 (σ y) (σ x)
       have i₂ := eq36889
       grind)
    | exact superpose eq36889 eq69917
    | (have j0 := eq69917 (σ y) (σ x)
       grind)
    | (have r₁ := eq69917 (σ y) (σ x)
       have r₂ := eq36889
       grind)
    | (have r₁ := eq69917 x x
       have r₂ := eq36889
       grind)
    | exact resolve eq69917 eq36889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36889 eq69917
  have eq70727 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq70605
  have eq70799 : (σ y) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70727
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq70727
    | exact resolve eq70727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70727
  have eq70833 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12564 x y
       have i₂ := eq70799
       grind)
    | exact superpose eq70799 eq12564
    | (have j0 := eq12564 x y
       grind)
    | exact resolve eq12564 eq70799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12564 eq70799
  have eq70941 : y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq70833
       have r₂ := eq36907
       grind)
    | exact resolve eq70833 eq36907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70833
  have eq71164 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq36907
       have i₂ := eq70941
       grind)
    | exact superpose eq70941 eq36907
    | exact resolve eq36907 eq70941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36907 eq70941
  have eq71211 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by grind
  clear eq71164
  have eq71212 : x = (M.op x x) := by grind
  clear eq71211
  have eq71938 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq71212
       grind)
    | exact superpose eq71212 eq19
    | exact resolve eq19 eq71212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71965 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq906 x X0
       have i₂ := eq71212
       grind)
    | exact superpose eq71212 eq906
    | exact resolve eq906 eq71212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq72118 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71965 X0
       have i₂ := eq71212
       grind)
    | exact superpose eq71212 eq71965
    | exact resolve eq71965 eq71212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71965
  have eq72145 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq71938 X0
       have i₂ := eq71212
       grind)
    | exact superpose eq71212 eq71938
    | exact resolve eq71938 eq71212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71212 eq71938
  have eq73797 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72118 (σ y)
       grind)
    | exact superpose eq72118 eq16
    | exact resolve eq16 eq72118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72118
  have eq74096 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq73797
       have i₂ := eq72145 y
       grind)
    | exact superpose eq72145 eq73797
    | exact resolve eq73797 eq72145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72145 eq73797
  have eq74097 : False := by grind
  exact eq74097

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_y_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq31 : y = (τ (σ y)) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq176 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1020 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1030 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1031 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1063 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1063 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1095 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1030
       grind)
    | exact superpose eq1030 eq39
    | exact resolve eq39 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1096 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1095
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1095
    | exact resolve eq1095 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq1098 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1096
    | exact resolve eq1096 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1098 eq1031
    | exact resolve eq1031 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1106
       have r₂ := eq27
       grind)
    | exact resolve eq1106 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1120 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1113 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1113
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1113
       grind)
    | exact resolve eq13 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1121 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1113 eq176
    | exact resolve eq176 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq1120 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1126 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1113 eq1121
    | exact resolve eq1121 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1131 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq1126 X1
       grind)
    | exact superpose eq1126 eq176
    | (have j1 := eq1126 X1
       grind)
    | exact resolve eq176 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1126 eq1131
    | (have j0 := eq1131 X0 X1
       have j1 := eq1126 X1
       grind)
    | exact resolve eq1131 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq1131
  have eq1139 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq1136 (M.op sF2 sF3) x
       grind)
    | exact superpose eq1136 eq26
    | (have j1 := eq1136 X0 (σ y)
       grind)
    | exact resolve eq26 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1162 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1139 x
       grind)
    | exact superpose eq1139 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1139 x
       grind)
    | exact resolve eq13 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1165 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1162 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1204 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1139 x
       have i₂ := eq1165 x
       grind)
    | exact superpose eq1165 eq1139
    | exact resolve eq1139 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1209 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1204
  have eq1232 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1209
       grind)
    | exact superpose eq1209 eq39
    | exact resolve eq39 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1237 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1232
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1232
    | exact resolve eq1232 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1243 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1237 eq1064
    | (have j0 := eq1064 (σ x)
       grind)
    | (have r₁ := eq1064 (σ x)
       have r₂ := eq1237
       grind)
    | exact resolve eq1064 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1244 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1243
  have eq1254 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1244 eq176
    | exact resolve eq176 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1256 : (σ x) = (k (σ x) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1244 eq1165
    | exact resolve eq1165 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1257 : (σ x) = (k (σ x) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1256
  have eq1262 : ∀ X0 : G, (M.op (k (σ x) x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1165 eq1254
    | exact resolve eq1254 eq1165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165 eq1254
  have eq1264 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1257 eq1262
    | exact resolve eq1262 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq1262
  have eq1272 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1264 eq26
    | (have j1 := eq1264 (σ y)
       grind)
    | exact resolve eq26 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1272
  have eq1294 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1285 eq27
    | exact resolve eq27 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1414 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1113
       have i₂ := eq1123 sF2
       grind)
    | exact superpose eq1123 eq1113
    | exact resolve eq1113 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq1123
  have eq1420 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq1414
  have eq1578 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1420 eq141
    | exact resolve eq141 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1586 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq1578
    | exact resolve eq1578 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1589 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1064 x
       grind)
    | (have r₁ := eq1586
       have r₂ := eq1064 x
       grind)
    | exact resolve eq1586 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1586
  have eq1600 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq1589
       grind)
    | exact superpose eq1589 eq176
    | exact resolve eq176 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1612 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1589 eq1600
    | exact resolve eq1600 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq1600
  have eq1618 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1612 y
       grind)
    | exact superpose eq1612 eq18
    | (have j1 := eq1612 y
       grind)
    | exact resolve eq18 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1618 eq27
    | exact resolve eq27 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1618 eq1021
    | (have r₁ := eq1021
       have r₂ := eq1618
       grind)
    | exact resolve eq1021 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1649 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1648
  have eq4195 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1649 eq1098
    | exact resolve eq1098 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq4210 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4195
  have eq4217 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4210
       have r₂ := eq1645
       grind)
    | exact resolve eq4210 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq4210
  have eq4262 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4217 eq176
    | exact resolve eq176 eq4217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4287 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4217 eq4262
    | exact resolve eq4262 eq4217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217 eq4262
  have eq4318 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = X0 ∨ (M.op (σ x) X1) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq4287 X1
       grind)
    | exact superpose eq4287 eq176
    | (have j1 := eq4287 X1
       grind)
    | exact resolve eq176 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4341 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4287 eq4318
    | (have j0 := eq4318 X0 X1
       have j1 := eq4287 X1
       grind)
    | exact resolve eq4318 eq4287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4287 eq4318
  have eq4374 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq4341 (M.op sF2 sF3) x
       grind)
    | exact superpose eq4341 eq26
    | (have j1 := eq4341 X0 (σ y)
       grind)
    | exact resolve eq26 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4416 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1612 eq4374
    | (have j0 := eq4374 X0
       have j1 := eq1612 X0
       grind)
    | exact resolve eq4374 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4374
  have eq4425 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4416 y
       grind)
    | exact superpose eq4416 eq18
    | (have j1 := eq4416 y
       grind)
    | exact resolve eq18 eq4416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4416
  have eq4456 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq4425
  have eq4467 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4456 eq26
    | exact resolve eq26 eq4456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4468 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4456 eq31
    | exact resolve eq31 eq4456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4456
  have eq4527 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4468
    | exact resolve eq4468 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4468
  have eq4528 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1618 eq4467
    | exact resolve eq4467 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4467
  have eq4530 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4527
       grind)
    | exact superpose eq4527 eq24
    | exact resolve eq24 eq4527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4527
  have eq4540 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4530
    | exact resolve eq4530 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530
  have eq4555 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq4540 eq1294
    | (have r₁ := eq1294
       have r₂ := eq4540
       grind)
    | exact resolve eq1294 eq4540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq4540
  have eq4562 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4555
  have eq4563 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4562
  have eq4566 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1618 eq4563
    | exact resolve eq4563 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq4563
  have eq4567 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4566
  have eq4583 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4567 eq27
    | exact resolve eq27 eq4567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4586 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4567 eq1021
    | (have r₁ := eq1021
       have r₂ := eq4567
       grind)
    | exact resolve eq1021 eq4567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq4588 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4586
  have eq4603 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4528 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq4528
       grind)
    | exact resolve eq13 eq4528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4604 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4528 eq176
    | exact resolve eq176 eq4528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4620 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603
  have eq4629 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4528 eq4604
    | exact resolve eq4604 eq4528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528 eq4604
  have eq5113 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4629 sF2
       have i₂ := eq4620 sF2
       grind)
    | exact superpose eq4620 eq4629
    | exact resolve eq4629 eq4620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629
  have eq5122 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5113
  have eq5240 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5122 eq141
    | exact resolve eq141 eq5122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq5122
  have eq5252 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5240
    | exact resolve eq5240 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq5354 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1062 x x
       have i₂ := eq5252
       grind)
    | exact superpose eq5252 eq1062
    | (have j0 := eq1062 x x
       grind)
    | (have r₁ := eq1062 x x
       have r₂ := eq5252
       grind)
    | exact resolve eq1062 eq5252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5252
  have eq5355 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5354
  have eq5356 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5355
  have eq5377 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq5356
       grind)
    | exact superpose eq5356 eq176
    | exact resolve eq176 eq5356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5383 : x = (k x (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4620 x
       have i₂ := eq5356
       grind)
    | exact superpose eq5356 eq4620
    | exact resolve eq4620 eq5356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq5388 : x = (k x (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5383
  have eq5403 : ∀ X0 : G, (M.op (k x (σ x)) X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4620 eq5377
    | exact resolve eq5377 eq4620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4620 eq5377
  have eq5406 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5388 eq5403
    | exact resolve eq5403 eq5388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5388 eq5403
  have eq5428 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5406 y
       grind)
    | exact superpose eq5406 eq18
    | (have j1 := eq5406 y
       grind)
    | exact resolve eq18 eq5406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5406
  have eq5461 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5428
  have eq5476 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5461
       grind)
    | exact superpose eq5461 eq24
    | exact resolve eq24 eq5461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5461
  have eq5485 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5476
    | exact resolve eq5476 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq5504 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5485 eq4583
    | exact resolve eq4583 eq5485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5485
  have eq5505 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq5504
  have eq5684 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4588 eq1098
    | exact resolve eq1098 eq4588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq4588
  have eq5699 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5684
  have eq5707 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5699
       have r₂ := eq4583
       grind)
    | exact resolve eq5699 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4583 eq5699
  have eq5790 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5707 eq176
    | exact resolve eq176 eq5707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5818 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5707 eq5790
    | exact resolve eq5790 eq5707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707 eq5790
  have eq5866 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = X0 ∨ (M.op (σ x) X1) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0
       have i₂ := eq5818 X1
       grind)
    | exact superpose eq5818 eq176
    | (have j1 := eq5818 X1
       grind)
    | exact resolve eq176 eq5818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5892 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5818 eq5866
    | (have j0 := eq5866 X0 X1
       have j1 := eq5818 X1
       grind)
    | exact resolve eq5866 eq5818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5818 eq5866
  have eq5943 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq5892 (M.op sF2 sF3) x
       grind)
    | exact superpose eq5892 eq26
    | (have j1 := eq5892 X0 (σ y)
       grind)
    | exact resolve eq26 eq5892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5892
  have eq5988 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1612 eq5943
    | (have j0 := eq5943 X0
       have j1 := eq1612 X0
       grind)
    | exact resolve eq5943 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq5943
  have eq5990 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5988 X0
       grind)
    | (have r₁ := eq5988 X0
       have r₂ := eq5505
       grind)
    | exact resolve eq5988 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5988
  have eq6001 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq5990 x
       grind)
    | exact superpose eq5990 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq5990 x
       grind)
    | exact resolve eq13 eq5990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6032 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6001
  have eq6140 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5990 x
       have i₂ := eq6032 x
       grind)
    | exact superpose eq6032 eq5990
    | exact resolve eq5990 eq6032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990
  have eq6177 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq6140
  have eq6278 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq6177
       grind)
    | exact superpose eq6177 eq39
    | exact resolve eq39 eq6177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6177
  have eq6295 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6278
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6278
    | exact resolve eq6278 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278
  have eq6305 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6295 eq1062
    | (have j0 := eq1062 (σ x) (σ x)
       grind)
    | (have r₁ := eq1062 (σ x) (σ x)
       have r₂ := eq6295
       grind)
    | exact resolve eq1062 eq6295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6295
  have eq6306 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6305
  have eq6307 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6306
  have eq6326 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6307 eq176
    | exact resolve eq176 eq6307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6334 : (σ x) = (k (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6307 eq6032
    | exact resolve eq6032 eq6307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6307
  have eq6339 : (σ x) = (k (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq6334
  have eq6357 : ∀ X0 : G, (M.op (k (σ x) x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6032 eq6326
    | exact resolve eq6326 eq6032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6032 eq6326
  have eq6359 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6339 eq6357
    | exact resolve eq6357 eq6339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339 eq6357
  have eq6389 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6359 eq26
    | (have j1 := eq6359 (σ y)
       grind)
    | exact resolve eq26 eq6359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6359
  have eq6438 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4567 eq6389
    | exact resolve eq6389 eq4567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567 eq6389
  have eq6443 : x = (M.op x y) := by
    first
    | (have r₁ := eq6438
       have r₂ := eq5505
       grind)
    | exact resolve eq6438 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505 eq6438
  have eq6446 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq18
    | exact resolve eq18 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6447 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq22
    | exact resolve eq22 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6449 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq39
    | exact resolve eq39 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq6450 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq1020
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq1020
    | (have r₁ := eq1020
       have r₂ := eq6443
       grind)
    | exact resolve eq1020 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq6451 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq6450
  have eq6453 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6447 eq20
    | exact resolve eq20 eq6447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6483 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6447 eq323
    | exact resolve eq323 eq6447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq7531 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6451 eq36
    | exact resolve eq36 eq6451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq6451
  have eq7541 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq7531
    | exact resolve eq7531 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7531
  have eq7546 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6453 eq7541
    | exact resolve eq7541 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7541
  have eq7554 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7546 eq1031
    | exact resolve eq1031 eq7546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq7546
  have eq7564 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq7554
  have eq9080 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7564 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq7564
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq7564
       grind)
    | exact resolve eq13 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9081 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7564 eq176
    | exact resolve eq176 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9100 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq9080 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9080
  have eq9109 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq7564 eq9081
    | exact resolve eq9081 eq7564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9081
  have eq9121 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 x
       have i₂ := eq9109 (M.op X0 X0)
       grind)
    | exact superpose eq9109 eq176
    | (have j1 := eq9109 X1
       grind)
    | exact resolve eq176 eq9109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9148 : ∀ X0 X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq9109 eq9121
    | (have j0 := eq9121 X0 X1
       have j1 := eq9109 X1
       grind)
    | exact resolve eq9121 eq9109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9109 eq9121
  have eq9160 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq9148 (M.op sF2 sF3) x
       grind)
    | exact superpose eq9148 eq26
    | (have j1 := eq9148 X0 (σ y)
       grind)
    | exact resolve eq26 eq9148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9148
  have eq9217 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9160 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq9160 (M.op x y)
       grind)
    | exact resolve eq13 eq9160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9253 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq9217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9217
  have eq9755 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9160 sF0
       have i₂ := eq9253 sF0
       grind)
    | exact superpose eq9253 eq9160
    | exact resolve eq9160 eq9253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9160
  have eq9782 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9755
  have eq9861 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9782 eq6449
    | exact resolve eq6449 eq9782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449 eq9782
  have eq9873 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9861
    | exact resolve eq9861 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9861
  have eq9880 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6453 eq9873
    | exact resolve eq9873 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9873
  have eq9898 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9880 eq1062
    | (have j0 := eq1062 (σ x) (σ x)
       grind)
    | (have r₁ := eq1062 (σ x) (σ x)
       have r₂ := eq9880
       grind)
    | exact resolve eq1062 eq9880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq9880
  have eq9899 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9898
  have eq9900 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9899
  have eq9932 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9900 eq176
    | exact resolve eq176 eq9900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9942 : (σ x) = (k (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9900 eq9253
    | exact resolve eq9253 eq9900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9900
  have eq9947 : (σ x) = (k (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9942
  have eq9963 : ∀ X0 : G, (M.op (k (σ x) (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9253 eq9932
    | exact resolve eq9932 eq9253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9253 eq9932
  have eq9966 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9947 eq9963
    | exact resolve eq9963 eq9947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9947 eq9963
  have eq9991 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9966 eq26
    | (have j1 := eq9966 (σ y)
       grind)
    | exact resolve eq26 eq9966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9966
  have eq10031 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9991
  have eq10051 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10031
  have eq15472 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7564
       have i₂ := eq9100 sF2
       grind)
    | exact superpose eq9100 eq7564
    | exact resolve eq7564 eq9100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7564 eq9100
  have eq15490 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq15472
  have eq15590 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15490 eq6483
    | exact resolve eq6483 eq15490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483 eq15490
  have eq15608 : x = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq15590
    | exact resolve eq15590 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15590
  have eq15615 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq15608
       have i₂ := eq6443
       grind)
    | exact superpose eq6443 eq15608
    | exact resolve eq15608 eq6443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6443 eq15608
  have eq15622 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1064 (M.op x y)
       grind)
    | (have r₁ := eq15615
       have r₂ := eq1064 (M.op x y)
       grind)
    | exact resolve eq15615 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq15615
  have eq15643 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15622 eq176
    | exact resolve eq176 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq15678 : ∀ X0 : G, (M.op (M.op x y) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq15622 eq15643
    | exact resolve eq15643 eq15622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15622 eq15643
  have eq15695 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15678 eq6446
    | exact resolve eq6446 eq15678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446 eq15678
  have eq15761 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15695 eq27
    | exact resolve eq27 eq15695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15695
  have eq15769 : y = (M.op x y) := by
    first
    | (have r₁ := eq15761
       have r₂ := eq6453
       grind)
    | exact resolve eq15761 eq6453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15761
  have eq16008 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15769
       grind)
    | exact superpose eq15769 eq24
    | exact resolve eq24 eq15769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15769
  have eq16029 : (σ x) = (σ y) := by
    first
    | exact superpose eq6447 eq16008
    | exact resolve eq16008 eq6447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6447 eq16008
  have eq16076 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16029 eq10051
    | (have r₁ := eq10051
       have r₂ := eq16029
       grind)
    | exact resolve eq10051 eq16029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10051 eq16029
  have eq16083 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16076
  have eq16149 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq16083 eq27
    | exact resolve eq27 eq16083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16083
  have eq16158 : False := by grind
  exact eq16158

/-- `Equation2994`: `x = ((y ◇ (z ◇ y)) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2994 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2994 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2994.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X3 : G, (M.op (M.op (M.op X0 X0) X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op x (M.op x x)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 X0) X0) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X0) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq19 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) = (k X1 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq35 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq19 X0 (M.op (M.op (M.op X0 X0) X0) X1)
       grind)
    | exact superpose eq19 eq33
    | exact resolve eq33 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) X1)
       have i₂ := eq35 X1 (τ X0)
       grind)
    | exact superpose eq35 eq17
    | exact resolve eq17 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 X1) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 X1) X1))
       have i₂ := eq40 (τ X0) X1
       grind)
    | exact superpose eq40 eq17
    | exact resolve eq17 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op X1 X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq139 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (M.op (M.op X1 X1) X1)))
       have i₂ := eq92 (τ X0) X1
       grind)
    | exact superpose eq92 eq17
    | exact resolve eq17 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq142 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139
    | exact resolve eq139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq213 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq77
    | exact resolve eq77 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq77
    | (have j0 := eq77 X2 X2
       grind)
    | exact resolve eq77 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq233 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq232 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq240 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq242 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq240 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq240 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq240 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq272 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (M.op (M.op X1 X1) X1))))
       have i₂ := eq142 (τ X0) X1
       grind)
    | exact superpose eq142 eq17
    | exact resolve eq17 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq421 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))
       have i₂ := eq276 (τ X0) X1
       grind)
    | exact superpose eq276 eq17
    | exact resolve eq17 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq421
    | exact resolve eq421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq666 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))
       have i₂ := eq425 (τ X0) X1
       grind)
    | exact superpose eq425 eq17
    | exact resolve eq17 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq666
    | exact resolve eq666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq693 : ∀ X0 : G, (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ≠ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ∨ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) = (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0
    first
    | (have i₁ := eq233 (σ (σ (σ (M.op (M.op X0 X0) X0))))
       have i₂ := eq142 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X0
       grind)
    | exact superpose eq142 eq233
    | (have j0 := eq233 (σ (σ (σ (M.op (M.op X0 X0) X0))))
       grind)
    | exact resolve eq233 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ≠ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ∨ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) = (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0
    first
    | (have i₁ := eq233 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       have i₂ := eq276 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X0
       grind)
    | exact superpose eq276 eq233
    | (have j0 := eq233 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       grind)
    | exact resolve eq233 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq716 : ∀ X0 : G, (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) = (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0
    first
    | (have j0 := eq695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq718 : ∀ X0 : G, (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) = (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0
    first
    | (have j0 := eq693 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq806 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) ≠ (σ (M.op (M.op X0 X0) X0)) ∨ (M.op (σ (M.op (M.op X0 X0) X0)) X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq242 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq35 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq35 eq242
    | (have j0 := eq242 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq242 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 : G, (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ≠ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) ∨ (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = (k X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq242 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X1
       have i₂ := eq142 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X0
       grind)
    | exact superpose eq142 eq242
    | (have j0 := eq242 (σ (σ (σ (M.op (M.op X0 X0) X0)))) X1
       grind)
    | exact resolve eq242 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq814 : ∀ X0 X1 : G, (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ≠ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) ∨ (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = (k X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq242 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1
       have i₂ := eq276 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X0
       grind)
    | exact superpose eq276 eq242
    | (have j0 := eq242 (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1
       grind)
    | exact resolve eq242 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq837 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = (k X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))) := by
    intro X0 X1
    first
    | (have j0 := eq814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq839 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = (k X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) := by
    intro X0 X1
    first
    | (have j0 := eq812 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq845 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = (k X1 (σ (M.op (M.op X0 X0) X0))) := by
    intro X0 X1
    first
    | (have j0 := eq806 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq859 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X1
       have i₂ := eq425 X1 X0
       grind)
    | exact superpose eq425 eq837
    | exact resolve eq837 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq861 : ∀ X0 X1 : G, (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq839 X0 X1
       have i₂ := eq276 X1 X0
       grind)
    | exact superpose eq276 eq839
    | exact resolve eq839 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq839
  have eq867 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 X0) X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq845
    | exact resolve eq845 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq845
  have eq2197 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))) (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq425 X1 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       have i₂ := eq861 X0 (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))
       grind)
    | exact superpose eq861 eq425
    | exact resolve eq425 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq2250 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2197 X0 X1
       have i₂ := eq718 X0
       grind)
    | exact superpose eq718 eq2197
    | exact resolve eq2197 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq2197
  have eq2966 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (M.op (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))) (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq425 X1 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))
       have i₂ := eq859 X0 (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0))))))
       grind)
    | exact superpose eq859 eq425
    | exact resolve eq425 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq3027 : ∀ X0 X1 : G, (k X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2966 X0 X1
       have i₂ := eq716 X0
       grind)
    | exact superpose eq716 eq2966
    | exact resolve eq2966 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq2966
  have eq4397 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) X2
       have i₂ := eq425 (τ X0) X1
       grind)
    | exact superpose eq425 eq216
    | (have j0 := eq216 X0 (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1)))))) X2
       grind)
    | exact resolve eq216 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq425
  have eq4485 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4397 X0 X1 X2
       have i₂ := eq672 X0 X1
       grind)
    | exact superpose eq672 eq4397
    | (have j0 := eq4397 X0 X1 X2
       grind)
    | exact resolve eq4397 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4397
  have eq4520 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) ∨ (σ X2) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4485 X0 X1 X2
       have i₂ := eq17 X0 X2
       grind)
    | exact superpose eq17 eq4485
    | (have j0 := eq4485 X0 X1 X2
       grind)
    | exact resolve eq4485 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4485
  have eq4546 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4520 X0 X1 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq4520 X0 X1 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | exact resolve eq4520 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4520
  have eq4569 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op (σ X2) X0) ∨ (σ X2) = (M.op (σ X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq4546 X0 x X2
       have i₂ := eq672 X0 x
       grind)
    | exact superpose eq672 eq4546
    | (have j0 := eq4546 X0 x X2
       grind)
    | exact resolve eq4546 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq4546
  have eq6655 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq213 X0 X1 X2
       grind)
    | exact superpose eq213 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq213 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq213 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (k X0 (σ X1))
       have r₂ := eq213 X0 X1 X2
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq6677 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6655 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6655
  have eq6678 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6677 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq6679 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6678 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq6678
    | (have j0 := eq6678 X0 X1 X2
       grind)
    | exact resolve eq6678 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6678
  have eq8864 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4569 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4569
    | exact resolve eq4569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8917 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4569 (σ X1) X0
       grind)
    | exact superpose eq4569 eq15
    | (have j1 := eq4569 (σ X1) X0
       grind)
    | exact resolve eq15 eq4569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4569
  have eq9043 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq8864 X0 (τ X1)
       grind)
    | exact superpose eq8864 eq17
    | (have j1 := eq8864 X0 (τ X1)
       grind)
    | exact resolve eq17 eq8864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq8864
  have eq11729 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9043 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9043
    | exact resolve eq9043 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9043
  have eq11877 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11729 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11729
    | (have j0 := eq11729 X0 X1
       grind)
    | exact resolve eq11729 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11729
  have eq24097 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8917 x y
       grind)
    | exact superpose eq8917 eq16
    | (have j1 := eq8917 x y
       grind)
    | exact resolve eq16 eq8917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24203 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq8917 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8917
  have eq25404 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24097
       have i₂ := eq11877 y x
       grind)
    | exact superpose eq11877 eq24097
    | (have j1 := eq11877 (σ y) (σ x)
       grind)
    | (have r₁ := eq24097
       have r₂ := eq11877 y x
       grind)
    | exact resolve eq24097 eq11877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25407 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25404
  have eq25411 : x ≠ x ∨ x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25407
       grind)
    | exact superpose eq25407 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25407
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25407
       grind)
    | exact resolve eq13 eq25407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25407
  have eq25446 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq25411
  have eq30754 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24203 x y
       have i₂ := eq25446
       grind)
    | exact superpose eq25446 eq24203
    | (have j0 := eq24203 x y
       grind)
    | exact resolve eq24203 eq25446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24203 eq25446
  have eq30761 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq30754
  have eq30762 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq30761
  have eq30780 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30762
       grind)
    | exact superpose eq30762 eq16
    | exact resolve eq16 eq30762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81362 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6679 X1 (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X0 X0) X0)))))))))) X2
       have i₂ := eq3027 X0 X1
       grind)
    | exact superpose eq3027 eq6679
    | exact resolve eq6679 eq3027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3027 eq6679
  have eq81504 : ∀ X0 X1 X2 : G, (σ (k X2 (τ X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81362 X0 X1 X2
       have i₂ := eq2250 X1 (τ X0)
       grind)
    | exact superpose eq2250 eq81362
    | (have j0 := eq81362 X0 X1 X2
       grind)
    | exact resolve eq81362 eq2250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81362
  have eq81545 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X2)) = (σ (k X2 (k (τ X0) (σ (σ (σ (σ (σ (σ (σ (σ (σ (M.op (M.op X1 X1) X1))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81504 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq81504
    | (have j0 := eq81504 X0 X1 X2
       grind)
    | exact resolve eq81504 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81504
  have eq81583 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (σ (k X2 (τ X0))) ∨ (k (σ X2) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq81545 X0 x X2
       have i₂ := eq2250 x (τ X0)
       grind)
    | exact superpose eq2250 eq81545
    | (have j0 := eq81545 X0 x X2
       grind)
    | exact resolve eq81545 eq2250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250 eq81545
  have eq81621 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (k (σ X2) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq81583 X0 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq81583
    | (have j0 := eq81583 X0 X2
       grind)
    | exact resolve eq81583 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq81583
  have eq81645 : ∀ X0 X2 : G, (M.op X0 (σ X2)) = (k (σ X2) X0) ∨ (k (σ X2) X0) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq81621 X0 X2
       have j1 := eq12 (σ X2) X0
       grind)
    | (have r₁ := eq81621 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq81621 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81621
  have eq81677 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81645 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81645
    | exact resolve eq81645 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81645
  have eq82590 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81677 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81677
  have eq83093 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq82590 (σ y) (σ x)
       have i₂ := eq30762
       grind)
    | exact superpose eq30762 eq82590
    | (have j0 := eq82590 (σ y) (σ x)
       grind)
    | (have r₁ := eq82590 (σ y) (σ x)
       have r₂ := eq30762
       grind)
    | (have r₁ := eq82590 x x
       have r₂ := eq30762
       grind)
    | exact resolve eq82590 eq30762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30762 eq82590
  have eq83192 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq83093
  have eq83273 : (σ x) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq83192
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq83192
    | exact resolve eq83192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83192
  have eq83892 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11877 y x
       have i₂ := eq83273
       grind)
    | exact superpose eq83273 eq11877
    | (have j0 := eq11877 y x
       grind)
    | exact resolve eq11877 eq83273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11877 eq83273
  have eq84020 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq83892
       have r₂ := eq30780
       grind)
    | exact resolve eq83892 eq30780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83892
  have eq84287 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq30780
       have i₂ := eq84020
       grind)
    | exact superpose eq84020 eq30780
    | exact resolve eq30780 eq84020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30780 eq84020
  have eq84341 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq84287
  have eq84342 : x = (M.op x x) := by grind
  clear eq84341
  have eq84351 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq84342
       grind)
    | exact superpose eq84342 eq19
    | exact resolve eq19 eq84342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq84353 : ∀ X0 : G, (k X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 x X0
       have i₂ := eq84342
       grind)
    | exact superpose eq84342 eq35
    | exact resolve eq35 eq84342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq84379 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq867 x X0
       have i₂ := eq84342
       grind)
    | exact superpose eq84342 eq867
    | exact resolve eq867 eq84342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq84521 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84379 X0
       have i₂ := eq84342
       grind)
    | exact superpose eq84342 eq84379
    | exact resolve eq84379 eq84342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84379
  have eq84547 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq84353 X0
       have i₂ := eq84342
       grind)
    | exact superpose eq84342 eq84353
    | exact resolve eq84353 eq84342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84353
  have eq84549 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84351 X0
       have i₂ := eq84342
       grind)
    | exact superpose eq84342 eq84351
    | exact resolve eq84351 eq84342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84342 eq84351
  have eq85177 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24097
       have i₂ := eq84547 y
       grind)
    | exact superpose eq84547 eq24097
    | exact resolve eq24097 eq84547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24097 eq84547
  have eq85189 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85177
       have i₂ := eq84549 y
       grind)
    | exact superpose eq84549 eq85177
    | exact resolve eq85177 eq84549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85177
  have eq85190 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq85189
  have eq85241 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq85190
       have i₂ := eq84521 (σ y)
       grind)
    | exact superpose eq84521 eq85190
    | exact resolve eq85190 eq84521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85190
  have eq85947 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85241
       grind)
    | exact superpose eq85241 eq16
    | exact resolve eq16 eq85241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86102 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq85947
       have i₂ := eq84521 (σ x)
       grind)
    | exact superpose eq84521 eq85947
    | exact resolve eq85947 eq84521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84521 eq85947
  have eq86125 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq86102
       have i₂ := eq84549 y
       grind)
    | exact superpose eq84549 eq86102
    | exact resolve eq86102 eq84549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84549 eq86102
  have eq86148 : False := by grind
  exact eq86148
