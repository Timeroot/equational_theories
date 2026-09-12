import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_x_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
  have eq1005 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq1016 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq1056 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1005 X1 (τ X0)
       grind)
    | exact superpose eq1005 eq17
    | (have j1 := eq1005 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1005
  have eq1182 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1056 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1056
    | exact resolve eq1056 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1248 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1182 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1182
    | (have j0 := eq1182 X0 X1
       grind)
    | exact resolve eq1182 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq2046 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1016 x y
       grind)
    | exact superpose eq1016 eq16
    | (have j1 := eq1016 x y
       grind)
    | exact resolve eq16 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq2165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2046
       have i₂ := eq1248 x y
       grind)
    | exact superpose eq1248 eq2046
    | (have j1 := eq1248 (σ x) (σ y)
       grind)
    | (have r₁ := eq2046
       have r₂ := eq1248 x y
       grind)
    | exact resolve eq2046 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq2046
  have eq2166 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2165
  have eq2170 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61 x y
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq61
    | exact resolve eq61 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2177 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2170
       have i₂ := eq2166
       grind)
    | exact superpose eq2166 eq2170
    | exact resolve eq2170 eq2166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166 eq2170
  have eq2186 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq2177
  have eq2228 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq61 (σ x) (σ y)
       have i₂ := eq2186
       grind)
    | exact superpose eq2186 eq61
    | exact resolve eq61 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2291 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2228
       have i₂ := eq2186
       grind)
    | exact superpose eq2186 eq2228
    | exact resolve eq2228 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186 eq2228
  have eq2302 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2291
  have eq2308 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2302
       have i₂ := eq391 y
       grind)
    | exact superpose eq391 eq2302
    | exact resolve eq2302 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq2318 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq444 y X0
       have i₂ := eq2308
       grind)
    | exact superpose eq2308 eq444
    | (have j0 := eq444 y X0
       grind)
    | (have r₁ := eq444 y x
       have r₂ := eq2308
       grind)
    | exact resolve eq444 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2319 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq446 y
       have i₂ := eq2308
       grind)
    | exact superpose eq2308 eq446
    | exact resolve eq446 eq2308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq2308
  have eq2344 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318
  have eq2352 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2319
       have i₂ := eq391 y
       grind)
    | exact superpose eq391 eq2319
    | exact resolve eq2319 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq2319
  have eq2353 : (σ y) = (σ (M.op y y)) := by grind
  clear eq2352
  have eq2354 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2344 X0
       have j1 := eq444 y X0
       grind)
    | (have r₁ := eq2344 X0
       have r₂ := eq444 y x
       grind)
    | exact resolve eq2344 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq2344
  have eq2370 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2353
       grind)
    | exact superpose eq2353 eq10
    | exact resolve eq10 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2424 : y = (M.op y y) := by
    first
    | (have i₁ := eq2370
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2370
    | exact resolve eq2370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2441 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq2424
       grind)
    | exact superpose eq2424 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq2424
       grind)
    | exact resolve eq12 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2477 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2441 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq2570 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2354 (σ X0)
       grind)
    | exact superpose eq2354 eq15
    | exact resolve eq15 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354
  have eq2590 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2570 X0
       have i₂ := eq2477 X0
       grind)
    | exact superpose eq2477 eq2570
    | exact resolve eq2570 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477 eq2570
  have eq2643 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq16
    | (have r₁ := eq16
       have r₂ := eq2590 x
       grind)
    | exact resolve eq16 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2684 : False := by grind
  exact eq2684

/-- `Equation2890`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2890 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2890 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2890.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq236 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq236 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq243 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq243
    | (have j0 := eq243 X0 X1
       grind)
    | exact resolve eq243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq747 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq251 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq251
    | exact resolve eq251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq251 x y
       grind)
    | exact superpose eq251 eq16
    | (have j1 := eq251 x y
       grind)
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq781 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq747 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq747
    | (have j0 := eq747 X0 X1
       grind)
    | exact resolve eq747 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq747
  have eq786 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq781 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq781
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq958 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq755
       have i₂ := eq786 x y
       grind)
    | exact superpose eq786 eq755
    | (have j1 := eq786 (σ x) (σ y)
       grind)
    | (have r₁ := eq755
       have r₂ := eq786 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq755
       have r₂ := eq786 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq755 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq786
  have eq961 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq958
  have eq963 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq961
       grind)
    | exact superpose eq961 eq10
    | exact resolve eq10 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq1000 : x = y ∨ x = y := by
    first
    | (have i₁ := eq963
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq963
    | exact resolve eq963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1001 : x = y := by grind
  clear eq1000
  have eq1048 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1001
       grind)
    | exact superpose eq1001 eq16
    | exact resolve eq16 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1049 : False := by grind
  exact eq1049

/-- `Equation2891`: `x = ((x ◇ (y ◇ z)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_x_pxy_Equation2891 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2891 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2891.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X1
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X2) (M.op (M.op X0 (M.op X2 X3)) X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op (M.op X0 (M.op X2 X3)) X3) X2
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) X1 X2
       have i₂ := eq16 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 (M.op X2 X1))) X2 X1
       have i₂ := eq16 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 (M.op sF0 x)) x)
       have i₂ := eq16 X0 sF0 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op X0 (M.op y sF0))
       have i₂ := eq16 X0 y sF0
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq176 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq16 X0 sF3 sF4
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) y) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq187 (M.op X0 (M.op sF0 x))
       have i₂ := eq16 X0 sF0 x
       grind)
    | exact superpose eq16 eq187
    | exact resolve eq187 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq197 (M.op X0 (M.op sF4 sF2))
       have i₂ := eq16 X0 sF4 sF2
       grind)
    | exact superpose eq16 eq197
    | exact resolve eq197 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq297 eq16
    | exact resolve eq16 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq313 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq300 eq16
    | exact resolve eq16 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq303 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq303
    | (have j0 := eq303 x
       grind)
    | exact resolve eq303 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ y) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq313 (M.op (M.op X0 (M.op sF3 x)) x)
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq313
    | exact resolve eq313 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq313
    | (have j0 := eq313 (σ x)
       grind)
    | exact resolve eq313 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq605 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op x y)) y)) = (M.op X1 (M.op x X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq179
    | exact resolve eq179 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq197 eq179
    | exact resolve eq179 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 X2 (M.op X0 X1) X1
       have i₂ := eq179 (M.op X0 X1) X1 X0
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op X1 X2)
       have i₂ := eq179 X0 X2 X1
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X2 X1) X2
       have i₂ := eq613 X2 X1 X0
       grind)
    | exact superpose eq613 eq16
    | exact resolve eq16 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 X1 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 X1) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 X1) (M.op X1 sF0))
       have i₂ := eq619 X0 X1 sF0
       grind)
    | exact superpose eq619 eq175
    | exact resolve eq175 eq619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op (M.op X3 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X1 (M.op X3 X2) (M.op (M.op X0 X2) X3)
       have i₂ := eq652 X0 X2 X3
       grind)
    | exact superpose eq652 eq179
    | exact resolve eq179 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq894 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq965 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq894 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq894 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq894 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq984 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k x y) := by
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
  have eq985 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq892
       grind)
    | exact superpose eq892 eq41
    | exact resolve eq41 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892
  have eq998 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq997
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq997
    | exact resolve eq997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1000 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq998
    | exact resolve eq998 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1000 eq893
    | exact resolve eq893 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1008
       have r₂ := eq27
       grind)
    | exact resolve eq1008 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1020 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1015 eq176
    | exact resolve eq176 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1021 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1015 eq184
    | exact resolve eq184 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1015 eq197
    | exact resolve eq197 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1015 eq313
    | exact resolve eq313 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1020
    | (have j0 := eq1020 (σ x)
       grind)
    | exact resolve eq1020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (σ x)) (M.op (M.op X0 (σ y)) (σ y))) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1020 eq16
    | exact resolve eq16 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1085 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1015 eq1064
    | exact resolve eq1064 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1100 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1085 eq613
    | exact resolve eq613 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1085 eq652
    | exact resolve eq652 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1106 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1021 eq1104
    | exact resolve eq1104 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1110 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1021 eq1100
    | exact resolve eq1100 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1100
  have eq1309 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1106 eq1022
    | exact resolve eq1022 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1312 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (σ x)) (M.op (M.op X0 (σ x)) (σ x))) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1106 eq16
    | exact resolve eq16 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1345 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1110 eq179
    | exact resolve eq179 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq2178 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (σ x))) = (M.op X1 (M.op (M.op (M.op X2 (σ y)) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1072 eq179
    | exact resolve eq179 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq2227 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X2) (σ x))) = (M.op X1 (M.op (M.op (M.op X2 (σ x)) (σ x)) X0)) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq1320 eq2178
    | exact resolve eq2178 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320 eq2178
  have eq6512 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1015 eq985
    | (have r₁ := eq985
       have r₂ := eq1015
       grind)
    | exact resolve eq985 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq6513 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6512
  have eq6514 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1000 eq6513
    | exact resolve eq6513 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6513
  have eq6523 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6514 eq197
    | exact resolve eq197 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6534 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6514 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq6514
       grind)
    | exact resolve eq13 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6550 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6534 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6584 : (σ x) = (M.op (k (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6550 eq6523
    | exact resolve eq6523 eq6550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6523 eq6550
  have eq6605 : (σ x) = (M.op (k (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1015 eq6584
    | exact resolve eq6584 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq6584
  have eq6618 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1000 eq6605
    | exact resolve eq6605 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6605
  have eq6633 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6618 eq1024
    | exact resolve eq1024 eq6618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq6618
  have eq6679 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq6633
  have eq6702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6514 eq6679
    | exact resolve eq6679 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514 eq6679
  have eq6722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq6702
    | exact resolve eq6702 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6702
  have eq6734 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6722
       have r₂ := eq27
       grind)
    | exact resolve eq6722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq6744 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6734 eq29
    | exact resolve eq29 eq6734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq6765 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq6744
    | exact resolve eq6744 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744
  have eq8195 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) X2) (M.op X1 (M.op X2 X3)) X3
       have i₂ := eq177 X1 X0 X2 X3
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8766 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X3 X2)) = (M.op (M.op X1 X3) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X1 (M.op X0 X2) X3 (M.op X3 X2)
       have i₂ := eq652 X0 X2 X3
       grind)
    | exact superpose eq652 eq178
    | exact resolve eq178 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq8774 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op (M.op X1 y) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8783 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op (M.op X1 (σ x)) (M.op X0 (σ x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1106 eq178
    | exact resolve eq178 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8784 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op (M.op X1 (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8894 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op (M.op X2 X1) X4))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X3 X4 (M.op X0 (M.op (M.op X2 X1) X4))
       have i₂ := eq178 X0 X2 X1 X4
       grind)
    | exact superpose eq178 eq179
    | exact resolve eq179 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8907 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X1) (M.op X3 X4))) = (M.op (M.op (M.op (M.op X0 X1) X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 (M.op (M.op X2 X1) (M.op X3 X4))) X3 X4
       have i₂ := eq178 X0 X2 X1 (M.op X3 X4)
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17107 : x = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op y (σ x)) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1312 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1312
    | (have j0 := eq1312 y x
       grind)
    | exact resolve eq1312 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq17386 : x = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ x)) y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17107
       have i₂ := eq845 y (M.op sF0 sF2) sF2 sF2
       grind)
    | (have i₁ := eq17107
       have i₂ := eq845 sF2 (M.op sF0 sF2) sF2 y
       grind)
    | exact superpose eq845 eq17107
    | exact resolve eq17107 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17107
  have eq17501 : (M.op x y) = (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (σ x) (σ x)) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6765 eq17386
    | exact resolve eq17386 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17386
  have eq17769 : (M.op (M.op x y) y) = (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17501 eq178
    | exact resolve eq178 eq17501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17775 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op (σ x) (σ x)) y)) (M.op (M.op x y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17501 eq16
    | exact resolve eq16 eq17501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17777 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) (σ x))) (M.op (M.op X1 (M.op x y)) (M.op (M.op (σ x) (σ x)) y))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq17501 eq177
    | exact resolve eq177 eq17501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq17779 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) y)) (M.op (M.op x y) (σ x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq17501 eq178
    | exact resolve eq178 eq17501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17501
  have eq17811 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (M.op (σ x) (σ x)) y) (σ x))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17779 X1 X1
       have i₂ := eq8766 (M.op (M.op sF2 sF2) y) X1 sF2 sF0
       grind)
    | (have i₁ := eq17779 X1 X1
       have i₂ := eq8766 sF0 X1 sF2 (M.op (M.op sF2 sF2) y)
       grind)
    | exact superpose eq8766 eq17779
    | exact resolve eq17779 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17779
  have eq17813 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) (σ x))) (M.op y (M.op (M.op (M.op X1 (M.op x y)) (σ x)) (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17777 X0 X1
       have i₂ := eq8894 (M.op X1 sF0) sF2 sF2 (M.op (M.op X0 X1) (M.op sF0 sF2)) y
       grind)
    | (have i₁ := eq17777 X0 X1
       have i₂ := eq8894 sF2 sF2 y (M.op (M.op X0 X1) (M.op sF0 sF2)) (M.op X1 sF0)
       grind)
    | exact superpose eq8894 eq17777
    | exact resolve eq17777 eq8894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17777
  have eq17814 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op (M.op (M.op (σ x) (σ x)) y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17775 X0
       have i₂ := eq8766 (M.op (M.op sF2 sF2) y) (M.op X0 sF0) sF2 sF0
       grind)
    | (have i₁ := eq17775 X0
       have i₂ := eq8766 sF0 (M.op X0 sF0) sF2 (M.op (M.op sF2 sF2) y)
       grind)
    | exact superpose eq8766 eq17775
    | exact resolve eq17775 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17775
  have eq17819 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1106 eq17769
    | exact resolve eq17769 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17769
  have eq17833 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (σ x) y) (M.op (σ x) (σ x)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17811 X0 X1
       have i₂ := eq845 (M.op sF2 sF2) (M.op X0 sF0) y sF2
       grind)
    | (have i₁ := eq17811 X0 X1
       have i₂ := eq845 sF2 (M.op X0 sF0) y (M.op sF2 sF2)
       grind)
    | exact superpose eq845 eq17811
    | exact resolve eq17811 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17811
  have eq17835 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) (M.op (M.op (M.op x y) (σ x)) (M.op (M.op (M.op X1 (M.op x y)) (σ x)) (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17813 X0 X1
       have i₂ := eq8766 (M.op sF0 sF2) (M.op X0 X1) (M.op (M.op (M.op X1 sF0) sF2) sF2) y
       grind)
    | (have i₁ := eq17813 X0 X1
       have i₂ := eq8766 y (M.op X0 X1) (M.op (M.op (M.op X1 sF0) sF2) sF2) (M.op sF0 sF2)
       grind)
    | exact superpose eq8766 eq17813
    | exact resolve eq17813 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17813
  have eq17836 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op (M.op (σ x) y) (M.op (σ x) (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17814 X0
       have i₂ := eq845 (M.op sF2 sF2) (M.op (M.op X0 sF0) sF0) y sF2
       grind)
    | (have i₁ := eq17814 X0
       have i₂ := eq845 sF2 (M.op (M.op X0 sF0) sF0) y (M.op sF2 sF2)
       grind)
    | exact superpose eq845 eq17814
    | exact resolve eq17814 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17814
  have eq17848 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) X1) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (σ x) (σ x)) (M.op y (σ x)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17833 X0 X1
       have i₂ := eq8766 y sF2 sF2 sF2
       grind)
    | (have i₁ := eq17833 X0 X1
       have i₂ := eq8766 sF2 sF2 sF2 y
       grind)
    | exact superpose eq8766 eq17833
    | exact resolve eq17833 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17833
  have eq17850 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) (M.op (σ x) (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) (M.op X1 (M.op x y))))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17835 X0 X1
       have i₂ := eq8894 (M.op sF0 sF2) sF2 (M.op X1 sF0) (M.op (M.op X0 X1) y) sF2
       grind)
    | (have i₁ := eq17835 X0 X1
       have i₂ := eq8894 (M.op X1 sF0) sF2 sF2 (M.op (M.op X0 X1) y) (M.op sF0 sF2)
       grind)
    | exact superpose eq8894 eq17835
    | exact resolve eq17835 eq8894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17835
  have eq17851 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op (M.op (σ x) (σ x)) (M.op y (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17836 X0
       have i₂ := eq8766 y sF2 sF2 sF2
       grind)
    | (have i₁ := eq17836 X0
       have i₂ := eq8766 sF2 sF2 sF2 y
       grind)
    | exact superpose eq8766 eq17836
    | exact resolve eq17836 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17836
  have eq17861 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (σ x) (σ x)) (M.op y (σ x)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq180 eq17848
    | exact resolve eq17848 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq17848
  have eq17862 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) (M.op y (M.op (M.op (M.op (M.op x y) (σ x)) (σ x)) (M.op X1 (M.op x y))))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17850 X0 X1
       have i₂ := eq8766 y (M.op X0 X1) (M.op (M.op (M.op sF0 sF2) sF2) (M.op X1 sF0)) sF2
       grind)
    | (have i₁ := eq17850 X0 X1
       have i₂ := eq8766 sF2 (M.op X0 X1) (M.op (M.op (M.op sF0 sF2) sF2) (M.op X1 sF0)) y
       grind)
    | exact superpose eq8766 eq17850
    | exact resolve eq17850 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17850
  have eq17863 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) (M.op (M.op (σ x) y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8783 eq17851
    | exact resolve eq17851 eq8783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8783 eq17851
  have eq17872 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X0 y) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1345 eq17861
    | exact resolve eq17861 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq17861
  have eq17873 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ x)) (M.op y (M.op (M.op (M.op X1 (M.op x y)) (M.op x y)) (σ x)))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2227 eq17862
    | exact resolve eq17862 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227 eq17862
  have eq17874 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) y) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17863 X0
       have i₂ := eq613 sF2 y (M.op (M.op X0 sF0) sF0)
       grind)
    | exact superpose eq613 eq17863
    | exact resolve eq17863 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17863
  have eq17879 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = (M.op (M.op X0 y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6765 eq17872
    | exact resolve eq17872 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17872
  have eq17880 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) (M.op (M.op X1 (M.op x y)) (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17873 X0 X1
       have i₂ := eq8195 (M.op X0 X1) y (M.op (M.op X1 sF0) sF0) sF2
       grind)
    | exact superpose eq8195 eq17873
    | exact resolve eq17873 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195 eq17873
  have eq17882 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X1 (M.op x y))) x) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8774 eq17880
    | exact resolve eq17880 eq8774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8774 eq17880
  have eq17884 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq737 eq17882
    | exact resolve eq17882 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq17882
  have eq17885 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6765 eq17884
    | exact resolve eq17884 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17884
  have eq17886 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) y) (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17879 eq17885
    | exact resolve eq17885 eq17879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17879 eq17885
  have eq17896 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17819 eq613
    | exact resolve eq613 eq17819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17949 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq323 eq17874
    | exact resolve eq17874 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq17874
  have eq18013 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6765 eq17949
    | exact resolve eq17949 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17949
  have eq18185 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (k (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17896 eq13
    | (have j0 := eq13 (M.op (M.op x y) (M.op x y)) X0
       grind)
    | exact resolve eq13 eq17896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17896
  have eq18328 : ∀ X0 : G, (k (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18185 X0
       grind)
    | (have r₁ := eq18185 X0
       have r₂ := eq18013
       grind)
    | exact resolve eq18185 eq18013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18185
  have eq18451 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18013 eq17886
    | exact resolve eq17886 eq18013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18457 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18013 eq303
    | exact resolve eq303 eq18013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18013
  have eq18483 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq18451
  have eq18503 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6765 eq18457
    | exact resolve eq18457 eq6765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6765 eq18457
  have eq18523 : (M.op (M.op x y) (M.op x y)) = (M.op (k (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18328 eq18503
    | exact resolve eq18503 eq18328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18503
  have eq18551 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq18483
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq18483
    | (have j1 := eq28 (k (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq18483 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20380 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18328 eq18483
    | exact resolve eq18483 eq18328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18328 eq18483
  have eq20585 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq20380
  have eq20757 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20585 eq42
    | exact resolve eq42 eq20585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20761 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq20757
    | exact resolve eq20757 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20757
  have eq20762 : (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6734 eq20761
    | exact resolve eq20761 eq6734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20761
  have eq20769 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20762 eq945
    | (have j0 := eq945 (σ (M.op (M.op x y) (M.op x y))) (σ x)
       grind)
    | (have r₁ := eq945 (σ (M.op (M.op x y) (M.op x y))) (σ x)
       have r₂ := eq20762
       grind)
    | exact resolve eq945 eq20762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20762
  have eq20770 : (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq20769
  have eq23060 : (M.op (M.op x y) (M.op x y)) = (k (k (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (k (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq18523
       have i₂ := eq28 (k (M.op sF0 sF0) sF0) sF0
       grind)
    | exact superpose eq28 eq18523
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18523 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18523
  have eq23126 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (k (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20585 eq23060
    | exact resolve eq23060 eq20585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20585 eq23060
  have eq23142 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq28 eq23126
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq23126 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23126
  have eq23150 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18551 eq23142
    | exact resolve eq23142 eq18551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18551 eq23142
  have eq25457 : (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23150 eq17886
    | exact resolve eq17886 eq23150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17886 eq23150
  have eq25489 : (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq25457
  have eq25502 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17819 eq25489
    | exact resolve eq25489 eq17819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17819 eq25489
  have eq25511 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq965 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq25502
       have r₂ := eq965 (M.op x y) x
       grind)
    | exact resolve eq25502 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq25502
  have eq25559 : (σ x) = (M.op (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25511 eq20770
    | exact resolve eq20770 eq25511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20770 eq25511
  have eq25610 : (σ x) = (M.op (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq25559
  have eq25641 : (σ x) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42 eq25610
    | exact resolve eq25610 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq25610
  have eq25655 : (σ x) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq25641
    | exact resolve eq25641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25641
  have eq25663 : (σ x) = (M.op (k (σ x) (σ x)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6734 eq25655
    | exact resolve eq25655 eq6734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734 eq25655
  have eq27532 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25663 eq1106
    | exact resolve eq1106 eq25663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq27585 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq27532
  have eq28871 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq27585
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq27585
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq27585 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27585
  have eq29000 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25663 eq28871
    | exact resolve eq28871 eq25663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25663 eq28871
  have eq29032 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq945 (σ x) (σ x)
       grind)
    | (have r₁ := eq29000
       have r₂ := eq945 (σ x) (σ x)
       grind)
    | exact resolve eq29000 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29000
  have eq29096 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29032 eq13
    | (have j0 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq13 (σ x) x
       have r₂ := eq29032
       grind)
    | exact resolve eq13 eq29032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29032
  have eq29121 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq29096 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29096
  have eq29977 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29121 eq26
    | (have j1 := eq29121 (σ y)
       grind)
    | exact resolve eq26 eq29121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29121
  have eq30296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1000 eq29977
    | exact resolve eq29977 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq29977
  have eq30386 : y = (M.op x y) := by
    first
    | (have r₁ := eq30296
       have r₂ := eq27
       grind)
    | exact resolve eq30296 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30296
  have eq30452 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq18
    | exact resolve eq18 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq30453 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq24
    | exact resolve eq24 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq30455 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq41
    | exact resolve eq41 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq30456 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq175
    | exact resolve eq175 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30457 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq181
    | exact resolve eq181 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq30459 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq187
    | exact resolve eq187 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq30460 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq303
    | exact resolve eq303 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq30462 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq984
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq984
    | (have r₁ := eq984
       have r₂ := eq30386
       grind)
    | exact resolve eq984 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq984
  have eq30463 : x = (k x (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq30462
  have eq30465 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30453 eq20
    | exact resolve eq20 eq30453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30475 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30453 eq371
    | exact resolve eq371 eq30453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq31008 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 (M.op x X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq605 eq178
    | exact resolve eq178 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31130 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) (M.op x y)) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31008 X0 X1
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq31008
    | exact resolve eq31008 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31008
  have eq31346 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq30452 eq175
    | exact resolve eq175 eq30452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq31348 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq30452 eq605
    | exact resolve eq605 eq30452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq31388 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq31348 X0
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq31348
    | exact resolve eq31348 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31348
  have eq31390 : x = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq31346
       have i₂ := eq30386
       grind)
    | exact superpose eq30386 eq31346
    | exact resolve eq31346 eq30386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30386 eq31346
  have eq31397 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x x)) := by
    intro X0
    first
    | exact superpose eq30457 eq31388
    | exact resolve eq31388 eq30457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30457 eq31388
  have eq31411 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq31390 eq178
    | exact resolve eq178 eq31390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31689 : ∀ X0 X1 : G, (M.op (M.op X1 X0) x) = (M.op (M.op X1 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq30456 eq178
    | exact resolve eq178 eq30456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30456
  have eq32127 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op x y)) = (M.op (M.op X1 x) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq30460 eq178
    | exact resolve eq178 eq30460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30460
  have eq32233 : (k (τ (σ x)) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq893 eq30475
    | exact resolve eq30475 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32282 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq32233
    | exact resolve eq32233 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32233
  have eq33399 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30463 eq30455
    | exact resolve eq30455 eq30463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30455 eq30463
  have eq33404 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33399
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33399
    | exact resolve eq33399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33399
  have eq33412 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33404 eq893
    | exact resolve eq893 eq33404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq33404
  have eq33678 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq31390 eq31411
    | exact resolve eq31411 eq31390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31390 eq31411
  have eq33889 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq33412
       grind)
    | exact superpose eq33412 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq33412
       grind)
    | exact resolve eq13 eq33412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33412
  have eq33910 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33889
  have eq36620 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op X1 (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq31130 eq613
    | exact resolve eq613 eq31130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36659 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op x X1))) = (M.op X2 (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq31130 eq179
    | exact resolve eq179 eq31130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31130
  have eq38261 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0))) = (M.op X1 (M.op x (M.op (M.op (M.op x y) (M.op x y)) X0))) := by
    intro X0 X1
    first
    | exact superpose eq36620 eq36620
    | exact resolve eq36620 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38494 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) x))) = (M.op X1 (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38261 x x
       have i₂ := eq8894 x sF0 sF0 x x
       grind)
    | (have i₁ := eq38261 x x
       have i₂ := eq8894 sF0 sF0 x x x
       grind)
    | exact superpose eq8894 eq38261
    | exact resolve eq38261 eq8894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8894 eq38261
  have eq38548 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) (M.op (M.op X0 (M.op x y)) x))) = (M.op X1 (M.op x (M.op x X0))) := by
    intro X0 X1
    first
    | exact superpose eq36620 eq38494
    | exact resolve eq38494 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38494
  have eq38580 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x x))) = (M.op X1 (M.op x (M.op x X0))) := by
    intro X0 X1
    first
    | exact superpose eq36659 eq38548
    | exact resolve eq38548 eq36659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36659 eq38548
  have eq38600 : ∀ X0 X1 : G, (M.op X1 (M.op X0 x)) = (M.op X1 (M.op x (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38580 X0 X1
       have i₂ := eq31397 X0
       grind)
    | exact superpose eq31397 eq38580
    | exact resolve eq38580 eq31397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38580
  have eq39552 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq8784
    | (have j0 := eq8784 X0 (σ x)
       grind)
    | exact resolve eq8784 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq43107 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 (M.op x y))) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) X0) x) := by
    intro X0
    first
    | exact superpose eq33678 eq31689
    | exact resolve eq31689 eq33678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31689 eq33678
  have eq43317 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq43107 x
       have i₂ := eq8907 sF0 sF0 sF0 x x
       grind)
    | exact superpose eq8907 eq43107
    | exact resolve eq43107 eq8907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8907 eq43107
  have eq43364 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op x X0))) = (M.op (M.op x x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq36620 eq43317
    | exact resolve eq43317 eq36620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36620 eq43317
  have eq43394 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op x X0))) = (M.op (M.op x X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq32127 eq43364
    | exact resolve eq43364 eq32127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43364
  have eq43413 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq43394 X0
       have i₂ := eq38600 X0 sF0
       grind)
    | exact superpose eq38600 eq43394
    | exact resolve eq43394 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600 eq43394
  have eq43521 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op (M.op X0 X1) (M.op x y)) x)) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq43413 eq178
    | exact resolve eq178 eq43413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43606 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op (M.op x y) (M.op (M.op x (M.op x y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq43521 X0 X1
       have i₂ := eq845 (M.op X0 X1) sF0 sF0 x
       grind)
    | (have i₁ := eq43521 X0 X1
       have i₂ := eq845 x sF0 sF0 (M.op X0 X1)
       grind)
    | exact superpose eq845 eq43521
    | exact resolve eq43521 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq43521
  have eq43690 : ∀ X0 X1 : G, (M.op (M.op x X1) X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq30452 eq43606
    | exact resolve eq43606 eq30452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43606
  have eq54388 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30452
       have i₂ := eq33910 sF0
       grind)
    | exact superpose eq33910 eq30452
    | exact resolve eq30452 eq33910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33910
  have eq54829 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54388 eq32282
    | exact resolve eq32282 eq54388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32282 eq54388
  have eq54839 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54829
  have eq54857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54839 eq14
    | exact resolve eq14 eq54839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54839
  have eq54866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq54857
    | exact resolve eq54857 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq54857
  have eq54869 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54866
       have r₂ := eq27
       grind)
    | exact resolve eq54866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54866
  have eq54870 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54869 eq27
    | exact resolve eq27 eq54869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54869
  have eq54900 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq54870
       have r₂ := eq30465
       grind)
    | exact resolve eq54870 eq30465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54870
  have eq54906 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq54900 eq27
    | exact resolve eq27 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq54907 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq54900 eq176
    | exact resolve eq176 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq54909 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq54900 eq184
    | exact resolve eq184 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq54911 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq54900 eq197
    | exact resolve eq197 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq54912 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq54900 eq300
    | exact resolve eq300 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq54913 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq54900 eq313
    | exact resolve eq313 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq54914 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq54900 eq331
    | exact resolve eq331 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq54919 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 (σ y)) (M.op X1 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq54900 eq8784
    | exact resolve eq8784 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54934 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq39552 eq54914
    | exact resolve eq54914 eq39552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54914
  have eq54936 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq30465 eq54906
    | exact resolve eq54906 eq30465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30465 eq54906
  have eq54939 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq54900 eq54934
    | exact resolve eq54934 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54934
  have eq54941 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54912 eq54939
    | exact resolve eq54939 eq54912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54939
  have eq54973 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq54941 eq8784
    | exact resolve eq8784 eq54941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54976 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq54941 eq28
    | exact resolve eq28 eq54941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq54941
  have eq55012 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq54976
       have r₂ := eq54936
       grind)
    | exact resolve eq54976 eq54936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54976
  have eq55013 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq54900 eq54973
    | exact resolve eq54973 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54973
  have eq55073 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq55012 eq30475
    | exact resolve eq30475 eq55012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30475 eq55012
  have eq55078 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq30 eq55073
    | exact resolve eq55073 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55073
  have eq55121 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq54907 eq54907
    | exact resolve eq54907 eq54907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54907
  have eq55646 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ y)) = (M.op (M.op X1 (σ x)) (M.op X0 (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq54911 eq178
    | exact resolve eq178 eq54911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55676 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op X1 (M.op (M.op X0 (σ x)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq54911 eq179
    | exact resolve eq179 eq54911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56109 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (σ x)) = (M.op (M.op X1 (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq54913 eq178
    | exact resolve eq178 eq54913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54913
  have eq57349 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq54912 eq55013
    | exact resolve eq55013 eq54912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54912
  have eq57429 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) (M.op X0 (σ x))) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq55013 eq54911
    | exact resolve eq54911 eq55013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54911
  have eq57477 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0
    first
    | exact superpose eq39552 eq57429
    | exact resolve eq57429 eq39552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39552 eq57429
  have eq57505 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57349
       have i₂ := eq613 sF2 sF2 sF2
       grind)
    | exact superpose eq613 eq57349
    | exact resolve eq57349 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57349
  have eq57544 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq609 eq57477
    | exact resolve eq57477 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq57477
  have eq57566 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq55121 eq57505
    | exact resolve eq57505 eq55121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55121 eq57505
  have eq57598 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq54900 eq57544
    | exact resolve eq57544 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57544
  have eq57739 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57566 eq8784
    | exact resolve eq8784 eq57566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8784
  have eq57746 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) X1) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq57566 eq178
    | exact resolve eq178 eq57566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57566
  have eq57786 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) X1) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq57746 X1 X1
       have i₂ := eq8766 sF3 X1 sF2 sF2
       grind)
    | (have i₁ := eq57746 X1 X1
       have i₂ := eq8766 sF2 X1 sF2 sF3
       grind)
    | exact superpose eq8766 eq57746
    | exact resolve eq57746 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8766 eq57746
  have eq57792 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x))) = (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq54900 eq57739
    | exact resolve eq57739 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57739
  have eq57811 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ x)) X1)) X1) := by
    intro X0 X1
    first
    | exact superpose eq55646 eq57786
    | exact resolve eq57786 eq55646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57786
  have eq57817 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ x)) X0) (σ x)) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq55646 eq57792
    | exact resolve eq57792 eq55646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55646 eq57792
  have eq57832 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq57811 X0 x
       have i₂ := eq178 X0 sF2 sF2 x
       grind)
    | exact superpose eq178 eq57811
    | exact resolve eq57811 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57811
  have eq58774 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ x) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57598 (M.op x sF3)
       have i₂ := eq179 sF2 sF3 x
       grind)
    | exact superpose eq179 eq57598
    | exact resolve eq57598 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57598
  have eq65204 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op x X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43690 (M.op X0 X1) X0
       have i₂ := eq613 X0 X1 sF0
       grind)
    | exact superpose eq613 eq43690
    | exact resolve eq43690 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq43690
  have eq72021 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op (M.op X0 X1) (σ x)) X3)) X3) = (M.op (M.op X2 (M.op X1 (σ x))) (M.op X0 (σ y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq54919 eq178
    | exact resolve eq178 eq54919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54919
  have eq72064 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ x)) (M.op X0 X1)) = (M.op (M.op X2 (M.op X1 (σ x))) (M.op X0 (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72021 X0 X1 X0 x
       have i₂ := eq178 X0 (M.op X0 X1) sF2 x
       grind)
    | exact superpose eq178 eq72021
    | exact resolve eq72021 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq72021
  have eq84116 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) X1) (σ x)) = (M.op (M.op (σ x) (M.op X0 (σ x))) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55013 eq56109
    | exact resolve eq56109 eq55013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55013
  have eq84405 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) X1) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq72064 eq84116
    | exact resolve eq84116 eq72064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72064 eq84116
  have eq94457 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) (σ x)) = (M.op (M.op (σ x) (M.op X0 (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq56109 eq57817
    | exact resolve eq57817 eq56109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56109 eq57817
  have eq94792 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) X0) (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq58774 eq94457
    | exact resolve eq94457 eq58774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58774 eq94457
  have eq94922 : ∀ X0 : G, (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq84405 eq94792
    | exact resolve eq94792 eq84405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84405 eq94792
  have eq95026 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) = (M.op (σ x) (M.op (M.op X0 (σ x)) (σ x))) := by
    intro X0
    first
    | exact superpose eq57832 eq94922
    | exact resolve eq94922 eq57832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57832 eq94922
  have eq95102 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq55676 eq95026
    | exact resolve eq95026 eq55676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55676 eq95026
  have eq106651 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | exact superpose eq95102 eq619
    | exact resolve eq619 eq95102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq106689 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (σ x) (M.op (σ y) (σ x))) ∨ (k (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq95102 eq13
    | (have j0 := eq13 (M.op (σ x) (σ x)) X0
       grind)
    | exact resolve eq13 eq95102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95102
  have eq106756 : ∀ X0 : G, (k (M.op (σ x) (σ x)) X0) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq106689 X0
       grind)
    | (have r₁ := eq106689 X0
       have r₂ := eq54909 (σ x)
       grind)
    | exact resolve eq106689 eq54909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54909 eq106689
  have eq106786 : (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq330 eq106651
    | exact resolve eq106651 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq106651
  have eq106904 : (σ x) = (k (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq106756 eq106786
    | exact resolve eq106786 eq106756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106756 eq106786
  have eq106998 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq54900 eq106904
    | exact resolve eq106904 eq54900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54900 eq106904
  have eq107111 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq106998 eq142
    | exact resolve eq142 eq106998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq106998
  have eq107116 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq30 eq107111
    | exact resolve eq107111 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq107111
  have eq107132 : x ≠ x ∨ x = (M.op (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq107116 eq945
    | (have j0 := eq945 (τ (M.op (σ x) (σ x))) x
       grind)
    | (have r₁ := eq945 (τ (M.op (σ x) (σ x))) x
       have r₂ := eq107116
       grind)
    | exact resolve eq945 eq107116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq107133 : x = (M.op (τ (M.op (σ x) (σ x))) x) := by grind
  clear eq107132
  have eq107163 : x ≠ x ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq107133 eq12
    | (have j0 := eq12 (τ (M.op (σ x) (σ x))) x
       grind)
    | (have r₁ := eq12 (τ (M.op (σ x) (σ x))) x
       have r₂ := eq107133
       grind)
    | exact resolve eq12 eq107133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107168 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op X0 (τ (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | exact superpose eq107133 eq179
    | exact resolve eq179 eq107133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq107198 : (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) ∨ (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by grind
  clear eq107163
  have eq107219 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (τ (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq107168 X0
       have i₂ := eq31397 X0
       grind)
    | exact superpose eq31397 eq107168
    | exact resolve eq107168 eq31397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31397 eq107168
  have eq107224 : x = (τ (M.op (σ x) (σ x))) ∨ (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq107116 eq107198
    | exact resolve eq107198 eq107116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107198
  have eq107261 : (τ (M.op (σ x) (σ x))) = (M.op (τ (M.op (σ x) (σ x))) x) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq107219 eq107224
    | exact resolve eq107224 eq107219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107219 eq107224
  have eq107284 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq107133 eq107261
    | exact resolve eq107261 eq107133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107261
  have eq107285 : x = (τ (M.op (σ x) (σ x))) := by grind
  clear eq107284
  have eq107319 : x = (M.op x x) := by
    first
    | exact superpose eq107285 eq107133
    | exact resolve eq107133 eq107285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107133
  have eq107320 : x = (k x x) := by
    first
    | exact superpose eq107285 eq107116
    | exact resolve eq107116 eq107285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107116 eq107285
  have eq107346 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq43413 x
       have i₂ := eq107319
       grind)
    | exact superpose eq107319 eq43413
    | exact resolve eq43413 eq107319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43413
  have eq107348 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq65204 X0 x
       have i₂ := eq107319
       grind)
    | exact superpose eq107319 eq65204
    | exact resolve eq65204 eq107319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65204
  have eq107366 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq107319
       grind)
    | exact superpose eq107319 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq107319
       grind)
    | exact resolve eq13 eq107319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107319
  have eq107401 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq107366 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107366
  have eq107444 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) X0)) = (k x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq107348 X0
       have i₂ := eq107401 (M.op x X0)
       grind)
    | exact superpose eq107401 eq107348
    | exact resolve eq107348 eq107401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107348
  have eq107446 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq30452 eq107346
    | exact resolve eq107346 eq30452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30452 eq107346
  have eq107482 : ∀ X0 : G, (k x (k x X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq107444 X0
       have i₂ := eq107401 X0
       grind)
    | exact superpose eq107401 eq107444
    | exact resolve eq107444 eq107401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107401 eq107444
  have eq107547 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq107320
       grind)
    | exact superpose eq107320 eq40
    | exact resolve eq40 eq107320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107320
  have eq107553 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq107547
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq107547
    | exact resolve eq107547 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107547
  have eq107872 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq107446 eq30459
    | exact resolve eq30459 eq107446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30459
  have eq107875 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq107446 eq32127
    | exact resolve eq32127 eq107446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32127 eq107446
  have eq107944 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq107875 eq107872
    | exact resolve eq107872 eq107875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107872 eq107875
  have eq107979 : (M.op x y) = (k x (k x (M.op x y))) := by
    first
    | exact superpose eq107482 eq107944
    | exact resolve eq107944 eq107482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107482 eq107944
  have eq108002 : (M.op x y) = (k x x) := by
    first
    | exact superpose eq55078 eq107979
    | exact resolve eq107979 eq55078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55078 eq107979
  have eq108304 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq108002
       grind)
    | exact superpose eq108002 eq40
    | exact resolve eq40 eq108002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq108002
  have eq108310 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq108304
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108304
    | exact resolve eq108304 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq108304
  have eq108312 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq107553 eq108310
    | exact resolve eq108310 eq107553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107553 eq108310
  have eq108562 : (σ x) = (σ y) := by
    first
    | exact superpose eq108312 eq30453
    | exact resolve eq30453 eq108312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30453 eq108312
  have eq108627 : False := by grind
  exact eq108627

/-- `Equation2919`: `x = ((y ◇ (x ◇ z)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2919 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2919 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2919.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  clear eq18
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq510 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq634 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq513 x y
       grind)
    | exact superpose eq513 eq16
    | (have j1 := eq513 x y
       grind)
    | exact resolve eq16 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq513 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3423 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq510 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq510
    | exact resolve eq510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq3488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3423 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3423
    | (have j0 := eq3423 X0 X1
       grind)
    | exact resolve eq3423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3423
  have eq6640 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq634
       have i₂ := eq3488 y x
       grind)
    | exact superpose eq3488 eq634
    | (have j1 := eq3488 (σ x) (σ y)
       grind)
    | (have r₁ := eq634
       have r₂ := eq3488 y x
       grind)
    | (have r₁ := eq634
       have r₂ := eq3488 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq634
       have r₂ := eq3488 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq634 eq3488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq6641 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq6640
  have eq17699 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq641 X1 X0
       have i₂ := eq513 X0 X1
       grind)
    | exact superpose eq513 eq641
    | (have j0 := eq641 X0 X1
       have j1 := eq513 X0 X1
       grind)
    | (have r₁ := eq641 X0 X0
       have r₂ := eq513 X0 X0
       grind)
    | exact resolve eq641 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq17700 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17699 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17699
  have eq17701 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq17700 X0 X1
       have j1 := eq641 X0 X1
       grind)
    | (have r₁ := eq17700 X0 X1
       have r₂ := eq641 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq17700 X0 X1
       have r₂ := eq641 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq17700 X0 X1
       have r₂ := eq641 X0 X1
       grind)
    | exact resolve eq17700 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641 eq17700
  have eq17927 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17701 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq17701
    | (have j0 := eq17701 (τ X0) (τ X1)
       grind)
    | exact resolve eq17701 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq17999 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17927 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq17927
    | (have j0 := eq17927 X0 X1
       grind)
    | exact resolve eq17927 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17927
  have eq18081 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17999 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq17999
    | (have j0 := eq17999 X0 X1
       grind)
    | exact resolve eq17999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17999
  have eq18135 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18081 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq18081
    | (have j0 := eq18081 X0 X1
       grind)
    | (have r₁ := eq18081 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq18081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18081
  have eq18187 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18135 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq18135
    | (have j0 := eq18135 X0 X1
       grind)
    | exact resolve eq18135 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18135
  have eq18235 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18187 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18187
    | (have j0 := eq18187 X0 X1
       grind)
    | exact resolve eq18187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18187
  have eq18265 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18235 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18235
    | (have j0 := eq18235 X0 X1
       grind)
    | exact resolve eq18235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18235
  have eq18283 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18265 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18265
    | (have j0 := eq18265 X0 X1
       grind)
    | exact resolve eq18265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18265
  have eq19563 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6641
       grind)
    | exact superpose eq6641 eq16
    | exact resolve eq16 eq6641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6641
  have eq19564 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19563
       have r₂ := eq22 x
       grind)
    | exact resolve eq19563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19563
  have eq19567 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19564
       grind)
    | exact superpose eq19564 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19564
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19564
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19564
       grind)
    | exact resolve eq13 eq19564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19564
  have eq19582 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19567
  have eq19925 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19582
       grind)
    | exact superpose eq19582 eq16
    | exact resolve eq16 eq19582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq19926 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq19925
       have r₂ := eq22 x
       grind)
    | exact resolve eq19925 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19925
  have eq19929 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19926
       grind)
    | exact superpose eq19926 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19926
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19926
       grind)
    | exact resolve eq13 eq19926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19930 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq19926
       grind)
    | exact superpose eq19926 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq19926
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19926
       grind)
    | exact resolve eq13 eq19926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19926
  have eq19945 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19930
  have eq19946 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19945
  have eq19947 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19929
  have eq19948 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq19947
  have eq19950 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19946
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19946
    | exact resolve eq19946 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19946
  have eq19951 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19948
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq19948
    | exact resolve eq19948 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19948
  have eq19995 : (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq19950
       have i₂ := eq19951
       grind)
    | exact superpose eq19951 eq19950
    | exact resolve eq19950 eq19951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19950 eq19951
  have eq20027 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq19995
  have eq20390 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq634
       have i₂ := eq20027
       grind)
    | exact superpose eq20027 eq634
    | exact resolve eq634 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq20397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq20390
  have eq20398 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq20397
  have eq20400 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq17701 x y
       grind)
    | (have r₁ := eq20398
       have r₂ := eq17701 x y
       grind)
    | (have r₁ := eq20398
       have r₂ := eq17701 y x
       grind)
    | exact resolve eq20398 eq17701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17701 eq20398
  have eq20404 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq20400
       grind)
    | exact superpose eq20400 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20400
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20400
       grind)
    | exact resolve eq13 eq20400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20400
  have eq20419 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq20404
  have eq20420 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq20419
  have eq20424 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20420
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20420
    | exact resolve eq20420 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20420
  have eq20429 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20424
       grind)
    | exact superpose eq20424 eq16
    | exact resolve eq16 eq20424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20424
  have eq20469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq20429
       have i₂ := eq20027
       grind)
    | exact superpose eq20027 eq20429
    | exact resolve eq20429 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20027
  have eq20474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq20469
  have eq20475 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq20474
  have eq20477 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20475
       grind)
    | exact superpose eq20475 eq10
    | exact resolve eq10 eq20475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20475
  have eq20646 : x = y ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq20477
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20477
    | exact resolve eq20477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20477
  have eq20648 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20646
       grind)
    | exact superpose eq20646 eq16
    | exact resolve eq16 eq20646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20646
  have eq20649 : (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq20648
       have r₂ := eq22 x
       grind)
    | exact resolve eq20648 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20648
  have eq20663 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq20649
       grind)
    | exact superpose eq20649 eq10
    | exact resolve eq10 eq20649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20649
  have eq20834 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq20663
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq20663
    | exact resolve eq20663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20663
  have eq20874 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq18283 x y
       have i₂ := eq20834
       grind)
    | exact superpose eq20834 eq18283
    | (have j0 := eq18283 x y
       grind)
    | (have r₁ := eq18283 x y
       have r₂ := eq20834
       grind)
    | (have r₁ := eq18283 y x
       have r₂ := eq20834
       grind)
    | exact resolve eq18283 eq20834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18283 eq20834
  have eq20880 : x = y ∨ (M.op x y) = (M.op y x) := by grind
  clear eq20874
  have eq20887 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20880
       grind)
    | exact superpose eq20880 eq16
    | exact resolve eq16 eq20880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20880
  have eq20888 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq20887
       have r₂ := eq22 x
       grind)
    | exact resolve eq20887 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20887
  have eq20891 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20888
       grind)
    | exact superpose eq20888 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20888
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20888
       grind)
    | exact resolve eq13 eq20888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq20906 : x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq20891
  have eq20932 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20906
       grind)
    | exact superpose eq20906 eq16
    | exact resolve eq16 eq20906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20906
  have eq20934 : (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq20932
       have r₂ := eq22 x
       grind)
    | exact resolve eq20932 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20932
  have eq20940 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20429
       have i₂ := eq20934
       grind)
    | exact superpose eq20934 eq20429
    | exact resolve eq20429 eq20934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20429 eq20934
  have eq20948 : (σ x) = (σ y) := by grind
  clear eq20940
  have eq20949 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20948
       grind)
    | exact superpose eq20948 eq16
    | exact resolve eq16 eq20948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20950 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20948
       grind)
    | exact superpose eq20948 eq10
    | exact resolve eq10 eq20948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20948
  have eq21119 : x = y := by
    first
    | (have i₁ := eq20950
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20950
    | exact resolve eq20950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20950
  have eq21120 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20949
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20949
    | exact resolve eq20949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20949
  have eq21121 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21120
       have i₂ := eq21119
       grind)
    | exact superpose eq21119 eq21120
    | exact resolve eq21120 eq21119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21119 eq21120
  have eq21122 : False := by grind
  exact eq21122

/-- `Equation2936`: `x = ((y ◇ (y ◇ x)) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation2936 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2936 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2936.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq32 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq36 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq36 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq36 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq37 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42
  have eq49 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq38 X1 X0
       grind)
    | (have r₁ := eq45 X1 X0
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq45 X0 (M.op X1 X1)
       have r₂ := eq38 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq38 (k X1 X1) X1
       grind)
    | exact resolve eq45 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq45
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq48
  have eq104 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq108 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq104 X0 X1
       have j1 := eq51 X1 X0
       grind)
    | (have r₁ := eq104 X1 X0
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq104 X0 X0
       have r₂ := eq51 X0 X0
       grind)
    | exact resolve eq104 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq104
  have eq244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq108 (σ X1) (σ X0)
       grind)
    | exact superpose eq108 eq15
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq108 X1 X0
       grind)
    | exact superpose eq108 eq244
    | exact resolve eq244 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq244
  have eq254 : False := by grind
  exact eq254

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation2982 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq43 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq43 (σ X0)
       grind)
    | exact superpose eq43 eq15
    | exact resolve eq15 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq57
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80
    | (have j0 := eq80 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq80 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq259 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq189
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq189
    | (have j1 := eq80 (σ x) (σ y)
       grind)
    | (have r₁ := eq189
       have r₂ := eq80 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq189
       have r₂ := eq80 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq189 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq189
  have eq262 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq259
  have eq353 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262
       grind)
    | exact superpose eq262 eq16
    | exact resolve eq16 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq354 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq353
       have r₂ := eq66 x
       grind)
    | exact resolve eq353 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq390 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq354
       grind)
    | exact superpose eq354 eq10
    | exact resolve eq10 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq407 : x = y := by
    first
    | (have i₁ := eq390
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq390
    | exact resolve eq390 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq451 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq407
       grind)
    | exact superpose eq407 eq16
    | exact resolve eq16 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq452 : False := by grind
  exact eq452

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_x_pyx_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq478 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 (M.op X2 X0)) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 (M.op X1 (M.op X2 X0)) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, x = (M.op X0 (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq479 eq57
    | exact resolve eq57 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq479
  have eq584 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X4 X3)) X4))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X2 (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X4 X3)) X4)) X1
       have i₂ := eq55 X3 (M.op X1 X2) X0 X4
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op (M.op X0 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op sF0 X0) (M.op (M.op X2 (M.op x X0)) x))
       have i₂ := eq55 X0 sF0 X2 x
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq588 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op (M.op X0 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op sF4 X0) (M.op (M.op X2 (M.op x X0)) x))
       have i₂ := eq55 X0 sF4 X2 x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
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
  have eq674 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X1 (M.op X1 X0) x
       have i₂ := eq56 X1 X1 X0 x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq853 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq45 X1
       grind)
    | exact superpose eq45 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq75
  have eq873 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq853 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq853
    | (have j0 := eq853 X0 x
       grind)
    | exact resolve eq853 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq924 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq873 X0
       have i₂ := eq674 (σ X0) sF2
       grind)
    | (have i₁ := eq873 X0
       have i₂ := eq674 sF2 (σ X0)
       grind)
    | exact superpose eq674 eq873
    | (have j0 := eq873 X0
       grind)
    | exact resolve eq873 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq938 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq924 X0
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq924
    | (have j0 := eq924 X0
       grind)
    | exact resolve eq924 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq924
  have eq1539 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq478 X0 X1 X2
       have i₂ := eq674 (M.op X1 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq478 X0 X1 X2
       have i₂ := eq674 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq674 eq478
    | exact resolve eq478 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq1926 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq674 (M.op X1 (M.op X0 (M.op X1 X2))) X0
       grind)
    | (have i₁ := eq671 X0 X1 X2
       have i₂ := eq674 X0 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq674 eq671
    | exact resolve eq671 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq674
  have eq2172 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1926 X1 X2 (M.op X1 (M.op X0 X2))
       have i₂ := eq1539 X2 X1 X0
       grind)
    | exact superpose eq1539 eq1926
    | exact resolve eq1926 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1539 eq1926
  have eq21365 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq586 X0 X1 X0
       have i₂ := eq2172 X0 (M.op sF0 X1) (M.op X0 (M.op X0 X1))
       grind)
    | (have i₁ := eq586 X0 X1 X2
       have i₂ := eq2172 (M.op X0 (M.op X2 X1)) (M.op sF0 X1) X2
       grind)
    | exact superpose eq2172 eq586
    | exact resolve eq586 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq21431 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq588 X0 X1 X0
       have i₂ := eq2172 X0 (M.op sF4 X1) (M.op X0 (M.op X0 X1))
       grind)
    | (have i₁ := eq588 X0 X1 X2
       have i₂ := eq2172 (M.op X0 (M.op X2 X1)) (M.op sF4 X1) X2
       grind)
    | exact superpose eq2172 eq588
    | exact resolve eq588 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq37714 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op X1 X2) X3) (M.op X4 (M.op X0 (M.op X4 X3))))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq584 X0 X1 X2 X3 X4
       have i₂ := eq2172 X4 (M.op (M.op X1 X2) X3) (M.op X0 (M.op X4 X3))
       grind)
    | (have i₁ := eq584 X0 X1 X2 X3 X4
       have i₂ := eq2172 (M.op X0 (M.op X4 X3)) (M.op (M.op X1 X2) X3) X4
       grind)
    | exact superpose eq2172 eq584
    | exact resolve eq584 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq2172
  have eq97316 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq938 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq938
    | (have j0 := eq938 y
       grind)
    | exact resolve eq938 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq97510 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97316
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq97316
    | exact resolve eq97316 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq97316
  have eq97545 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq97510
    | exact resolve eq97510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97510
  have eq97558 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq97545
    | exact resolve eq97545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97545
  have eq193522 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq503
       grind)
    | exact superpose eq503 eq103
    | exact resolve eq103 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq503
  have eq193534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq193522 eq97558
    | exact resolve eq97558 eq193522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97558 eq193522
  have eq193553 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq193534
       have r₂ := eq28
       grind)
    | exact resolve eq193534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193534
  have eq193731 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq193553 eq37714
    | exact resolve eq37714 eq193553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193553
  have eq193817 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21431 eq193731
    | exact resolve eq193731 eq21431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21431 eq193731
  have eq193818 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq193817
  have eq194170 : ∀ X0 X1 X2 : G, x = (M.op (M.op X0 x) (M.op (M.op (M.op x y) X1) (M.op X2 (M.op X0 (M.op X2 X1))))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37714 X0 x x X1 X2
       have i₂ := eq193818
       grind)
    | exact superpose eq193818 eq37714
    | exact resolve eq37714 eq193818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37714 eq193818
  have eq194256 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21365 eq194170
    | exact resolve eq194170 eq21365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21365 eq194170
  have eq194257 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq194256
  have eq194885 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq194257 eq30
    | exact resolve eq30 eq194257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq194257
  have eq195092 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq194885
    | exact resolve eq194885 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq194885
  have eq195093 : x = y := by grind
  clear eq195092
  have eq195115 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq195093
       grind)
    | exact superpose eq195093 eq19
    | exact resolve eq19 eq195093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq195116 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq195093
       grind)
    | exact superpose eq195093 eq25
    | exact resolve eq25 eq195093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq195093
  have eq195321 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq195116
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq195116
    | exact resolve eq195116 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq195116
  have eq195358 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq195321 eq27
    | exact resolve eq27 eq195321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq195321
  have eq199282 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq195358 eq69
    | exact resolve eq69 eq195358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq195358
  have eq199642 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq199282
       have i₂ := eq195115
       grind)
    | exact superpose eq195115 eq199282
    | exact resolve eq199282 eq195115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195115 eq199282
  have eq199778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq199642 eq15
    | exact resolve eq15 eq199642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199642
  have eq199854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq199778
    | exact resolve eq199778 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq199778
  have eq199875 : False := by grind
  exact eq199875

/-- `Equation2982`: `x = ((y ◇ (z ◇ x)) ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation2982 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2982 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2982.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
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
  have eq70 : y ≠ (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq2706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2706
    | exact resolve eq2706 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706
  have eq2710 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2707
       have r₂ := eq28
       grind)
    | exact resolve eq2707 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707
  have eq2712 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq2710
    | exact resolve eq2710 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2710
  have eq2716 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2712 eq28
    | exact resolve eq28 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2718 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2712 eq71
    | (have r₁ := eq71
       have r₂ := eq2712
       grind)
    | exact resolve eq71 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq2712
  have eq2728 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2718
  have eq2729 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2728
  have eq2739 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2729 eq88
    | exact resolve eq88 eq2729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2729
  have eq2743 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2739
  have eq2748 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2743
       have r₂ := eq2716
       grind)
    | exact resolve eq2743 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716 eq2743
  have eq2753 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq2748 eq30
    | exact resolve eq30 eq2748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2779 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2753
    | exact resolve eq2753 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq2780 : y = (M.op x y) ∨ x = y := by grind
  clear eq2779
  have eq2784 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2780 eq21
    | exact resolve eq21 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2787 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq2780 eq70
    | (have r₁ := eq70
       have r₂ := eq2780
       grind)
    | exact resolve eq70 eq2780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2780
  have eq2807 : y ≠ y ∨ x = y ∨ y = (k x y) := by grind
  clear eq2787
  have eq2808 : y = (k x y) ∨ x = y := by grind
  clear eq2807
  have eq2823 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2784
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2784
    | exact resolve eq2784 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq2868 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq2808
       grind)
    | exact superpose eq2808 eq49
    | exact resolve eq49 eq2808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq2808
  have eq2873 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2868
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2868
    | exact resolve eq2868 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq2904 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2873 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq2905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2904
  have eq2911 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq2905
    | exact resolve eq2905 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2905
  have eq2931 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2911 eq28
    | exact resolve eq28 eq2911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq2949 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2931
       have r₂ := eq2823
       grind)
    | exact resolve eq2931 eq2823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823 eq2931
  have eq2955 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2949 eq30
    | exact resolve eq30 eq2949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2949
  have eq2986 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2955
    | exact resolve eq2955 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2955
  have eq2987 : x = y := by grind
  clear eq2986
  have eq2991 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2987
       grind)
    | exact superpose eq2987 eq19
    | exact resolve eq19 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2992 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2987
       grind)
    | exact superpose eq2987 eq25
    | exact resolve eq25 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2987
  have eq3020 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2992
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2992
    | exact resolve eq2992 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2992
  have eq3026 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3020 eq27
    | exact resolve eq27 eq3020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3020
  have eq3086 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3026 eq69
    | exact resolve eq69 eq3026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq3026
  have eq3105 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3086
       have i₂ := eq2991
       grind)
    | exact superpose eq2991 eq3086
    | exact resolve eq3086 eq2991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991 eq3086
  have eq3222 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3105 eq15
    | exact resolve eq15 eq3105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3105
  have eq3248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq3222
    | exact resolve eq3222 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq3222
  have eq3253 : False := by grind
  exact eq3253
