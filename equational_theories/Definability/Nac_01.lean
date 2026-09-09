import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation4502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq28 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 X1)) = (τ (k X2 (k (σ X0) (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq37 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq9 x X2 X4 X5
       have i₂ := eq9 x X2 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X2 X2) x x
       have i₂ := eq9 (M.op x x) X2 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (k X0 (τ X1)) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X2 (k (σ X0) X1)
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq28
    | exact resolve eq28 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq269 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq273 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq277 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op X0 (k X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2 X3
       have i₂ := eq276 X1
       grind)
    | exact superpose eq276 eq9
    | exact resolve eq9 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (k X2 X2) (k X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq42 X0 X1 X0 X3
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq42
    | exact resolve eq42 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq309 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (k (k X2 X2) (k X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq283 X0 X1 X2 X3
       have i₂ := eq276 (k X2 X2)
       grind)
    | exact superpose eq276 eq283
    | exact resolve eq283 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq310 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X0) = X0 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 X1
       have i₂ := eq276 X1
       grind)
    | exact superpose eq276 eq280
    | (have j0 := eq280 X0 X1
       grind)
    | exact resolve eq280 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq311 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq276 X1
       grind)
    | exact superpose eq276 eq279
    | (have j0 := eq279 X0 X0
       grind)
    | exact resolve eq279 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X1) = (M.op (k X0 X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X0 X0 X1 X2 X3
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq37
    | exact resolve eq37 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X1)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X0 X1 (M.op X0 X1) X2 X3
       have i₂ := eq276 (M.op X0 X1)
       grind)
    | exact superpose eq276 eq37
    | exact resolve eq37 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq336 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (τ X0)) = (M.op X3 (τ (k X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq277 X3 (τ X0) X1 X2
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq277
    | exact resolve eq277 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (k X2 X2) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq276 (k X2 X2)
       have i₂ := eq277 (k X2 X2) X2 X0 X1
       grind)
    | exact superpose eq277 eq276
    | exact resolve eq276 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq354 : ∀ X0 X1 : G, (M.op X0 (k X1 X1)) = (k (k X1 X1) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1 x x
       have i₂ := eq349 x x X1
       grind)
    | exact superpose eq349 eq277
    | exact resolve eq277 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq360 : ∀ X2 X3 : G, (k (k X2 X2) (k X2 X2)) = (M.op X3 (k (k X2 X2) (k X2 X2))) := by
    intro X2 X3
    first
    | (have i₁ := eq309 x x X2 X3
       have i₂ := eq349 x x X2
       grind)
    | exact superpose eq349 eq309
    | exact resolve eq309 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq363 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1 x x
       have i₂ := eq349 x x X1
       grind)
    | exact superpose eq349 eq318
    | exact resolve eq318 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq365 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 X1 x x
       have i₂ := eq349 x x (M.op X0 X1)
       grind)
    | exact superpose eq349 eq320
    | exact resolve eq320 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq376 : ∀ X0 X3 : G, (M.op X3 (τ (k X0 X0))) = (k (k (τ X0) (τ X0)) (k (τ X0) (τ X0))) := by
    intro X0 X3
    first
    | (have i₁ := eq336 X0 x x X3
       have i₂ := eq349 x x (τ X0)
       grind)
    | exact superpose eq349 eq336
    | exact resolve eq336 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq349
  have eq394 : ∀ X2 : G, (k (k X2 X2) (k X2 X2)) = (k (k (k X2 X2) (k X2 X2)) (k (k X2 X2) (k X2 X2))) := by
    intro X2
    first
    | (have i₁ := eq360 X2 x
       have i₂ := eq354 x (k X2 X2)
       grind)
    | exact superpose eq354 eq360
    | exact resolve eq360 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq399 : ∀ X0 X3 : G, (M.op X3 (τ (k X0 X0))) = (k (τ (k X0 X0)) (τ (k X0 X0))) := by
    intro X0 X3
    first
    | (have i₁ := eq376 X0 X3
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq376
    | exact resolve eq376 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq402 : ∀ X0 X3 : G, (M.op X3 (τ (k X0 X0))) = (τ (k (k X0 X0) (k X0 X0))) := by
    intro X0 X3
    first
    | (have i₁ := eq399 X0 X3
       have i₂ := eq28 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq28 eq399
    | exact resolve eq399 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq403 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 (τ X0) X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq278
    | (have j0 := eq278 (τ X0) X1
       grind)
    | exact resolve eq278 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq310 (σ x) (σ y)
       grind)
    | exact superpose eq310 eq16
    | (have j1 := eq310 (σ x) (σ x)
       grind)
    | exact resolve eq16 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2402 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) ≠ (k (k X0 X0) (k X0 X0)) ∨ (k (k (k X0 X0) (k X0 X0)) X1) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq278 (k (k X0 X0) (k X0 X0)) X1
       have i₂ := eq394 X0
       grind)
    | exact superpose eq394 eq278
    | (have j0 := eq278 (k (k X0 X0) (k X0 X0)) X1
       grind)
    | (have r₁ := eq278 (k (k x x) (k x x)) X1
       have r₂ := eq394 x
       grind)
    | exact resolve eq278 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2403 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) ≠ (k (k X0 X0) (k X0 X0)) ∨ (k X1 X1) = X1 ∨ (k X1 (k (k X0 X0) (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq311 X1 (k (k X0 X0) (k X0 X0))
       have i₂ := eq394 X0
       grind)
    | exact superpose eq394 eq311
    | (have j0 := eq311 X1 X1
       grind)
    | (have r₁ := eq311 X0 (k (k x x) (k x x))
       have r₂ := eq394 x
       grind)
    | exact resolve eq311 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq2413 : ∀ X0 X1 : G, (k X1 (k (k X0 X0) (k X0 X0))) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq2414 : ∀ X0 X1 : G, (k (k (k X0 X0) (k X0 X0)) X1) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2402
  have eq2418 : ∀ X0 X1 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = (k (k (k X0 X0) (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2414 X0 X1
       have i₂ := eq354 X1 (k X0 X0)
       grind)
    | exact superpose eq354 eq2414
    | exact resolve eq2414 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq2425 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) = (k (k (k X0 X0) (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2418 X0 X1
       have i₂ := eq394 X0
       grind)
    | (have i₁ := eq2418 X0 X1
       have i₂ := eq394 (k X0 X0)
       grind)
    | exact superpose eq394 eq2418
    | exact resolve eq2418 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq2418
  have eq2430 : ∀ X0 X1 : G, (k X1 (k (τ (k X0 X0)) (τ (k X0 X0)))) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2413 (τ X0) X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq2413
    | (have j0 := eq2413 X0 X1
       grind)
    | exact resolve eq2413 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2470 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (k (k X1 X1) (k X1 X1)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (k (k X1 X1) (k X1 X1)) X0
       have i₂ := eq2413 X1 (σ X0)
       grind)
    | exact superpose eq2413 eq20
    | (have j1 := eq2413 X0 (σ X0)
       grind)
    | exact resolve eq20 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2491 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (τ (k (k X1 X1) (k X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2470 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2470
    | (have j0 := eq2470 X0 X1
       grind)
    | exact resolve eq2470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470
  have eq2518 : ∀ X0 X1 : G, (k X1 (τ (k (k X0 X0) (k X0 X0)))) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2430 X0 X1
       have i₂ := eq28 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq28 eq2430
    | (have j0 := eq2430 X0 X1
       grind)
    | exact resolve eq2430 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2430
  have eq3097 : (k (σ x) (σ y)) ≠ (σ (k x y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq484
       have i₂ := eq310 x y
       grind)
    | exact superpose eq310 eq484
    | (have j1 := eq310 (σ x) (σ x)
       grind)
    | exact resolve eq484 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq484
  have eq3098 : y = (k y y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq3097
       have r₂ := eq15 x y
       grind)
    | exact resolve eq3097 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3097
  have eq9690 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (k (k (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2425 (M.op X0 X1) X1
       have i₂ := eq365 X0 X1
       grind)
    | exact superpose eq365 eq2425
    | exact resolve eq2425 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq12526 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15 y y
       have i₂ := eq3098
       grind)
    | exact superpose eq3098 eq15
    | exact resolve eq15 eq3098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3098
  have eq12527 : x = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq12526
  have eq66073 : ∀ X0 X1 X2 : G, (τ (k (σ X0) (σ X0))) = (M.op X1 (τ (σ X0))) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq402 (σ X0) x
       have i₂ := eq2491 X0 X1
       grind)
    | exact superpose eq2491 eq402
    | (have j1 := eq2491 X0 X2
       grind)
    | exact resolve eq402 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66074 : ∀ X0 X1 X2 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq403 (σ X0) X1
       have i₂ := eq2491 X0 X2
       grind)
    | exact superpose eq2491 eq403
    | (have j0 := eq403 (σ X0) X1
       have j1 := eq2491 X0 X2
       grind)
    | exact resolve eq403 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq66112 : ∀ X0 X1 X2 : G, (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq66074 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66074
  have eq66137 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66112 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66112
    | (have j0 := eq66112 X0 X1 X2
       grind)
    | exact resolve eq66112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66112
  have eq66138 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (τ (k (σ X0) (σ X0))) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66073 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66073
    | (have j0 := eq66073 X0 X1 X2
       grind)
    | exact resolve eq66073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66073
  have eq66163 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 (τ (σ X0))) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66138 X0 X1 X2
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq66138
    | (have j0 := eq66138 X0 X1 X2
       grind)
    | exact resolve eq66138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66138
  have eq66177 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 X0) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66163 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66163
    | (have j0 := eq66163 X0 X1 X2
       grind)
    | exact resolve eq66163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66163
  have eq67523 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (k X0 X0) ∨ (k X0 (τ (k (k X2 X2) (k X2 X2)))) = X0 ∨ (k X0 (τ (k (k X3 X3) (k X3 X3)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq66137 X0 X1 X2
       have i₂ := eq66177 X0 X1 X3
       grind)
    | exact superpose eq66177 eq66137
    | (have j0 := eq66137 X0 X1 X2
       have j1 := eq66177 X0 X1 X2
       grind)
    | exact resolve eq66137 eq66177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66137 eq66177
  have eq67544 : ∀ X0 X1 X2 : G, (k X0 (τ (k (k X1 X1) (k X1 X1)))) = X0 ∨ (k X0 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67523 X0 X2 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67523
  have eq69014 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X0) = (k X0 (τ (k (k X1 X1) (k X1 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq67544 X0 X1 (τ (k (k X1 X1) (k X1 X1)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67544
  have eq69015 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 (τ (k (k X1 X1) (k X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69014 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69014
  have eq69021 : ∀ X0 X1 : G, (k X0 (τ (k (k X1 X1) (k X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69015 X0 X1
       have j1 := eq2518 X1 X0
       grind)
    | (have r₁ := eq69015 (τ (k (k X0 X0) (k X0 X0))) X1
       have r₂ := eq2518 X0 (τ (k (k X0 X0) (k X0 X0)))
       grind)
    | (have r₁ := eq69015 X1 X1
       have r₂ := eq2518 X0 X1
       grind)
    | exact resolve eq69015 eq2518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2518 eq69015
  have eq69820 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15 x x
       have i₂ := eq12527
       grind)
    | exact superpose eq12527 eq15
    | exact resolve eq15 eq12527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12527
  have eq69827 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq69820
  have eq69927 : ∀ X0 X1 : G, (k X1 (k (k X0 (τ (σ X0))) (τ (k (σ X0) (σ X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69021 X1 (σ X0)
       have i₂ := eq55 X0 (σ X0) (k (σ X0) (σ X0))
       grind)
    | exact superpose eq55 eq69021
    | exact resolve eq69021 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq70459 : ∀ X0 X1 : G, (k X1 (k (k X0 (τ (σ X0))) (k X0 (τ (σ X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69927 X0 X1
       have i₂ := eq20 (σ X0) X0
       grind)
    | exact superpose eq20 eq69927
    | exact resolve eq69927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69927
  have eq70969 : ∀ X0 X1 : G, (k X1 (k (k X0 X0) (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70459 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70459
    | exact resolve eq70459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70459
  have eq71271 : ∀ X0 X1 X2 : G, (k X2 (k (M.op X0 X1) (M.op X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70969 (M.op X0 X1) X2
       have i₂ := eq9690 X0 X1 (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq9690 eq70969
    | exact resolve eq70969 eq9690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690
  have eq72403 : ∀ X0 X1 X2 : G, (τ X0) = (τ (k X0 (k (σ (M.op X1 X2)) (σ (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (M.op X1 X2) (M.op X1 X2) X0
       have i₂ := eq71271 X1 X2 (τ X0)
       grind)
    | exact superpose eq71271 eq29
    | exact resolve eq29 eq71271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq71271
  have eq78097 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (k (σ (M.op X1 X2)) (σ (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k (σ (M.op X1 X2)) (σ (M.op X1 X2))))
       have i₂ := eq72403 X0 X1 X2
       grind)
    | exact superpose eq72403 eq11
    | exact resolve eq11 eq72403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72403
  have eq78298 : ∀ X0 X1 X2 : G, (k X0 (k (σ (M.op X1 X2)) (σ (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78097 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78097
    | exact resolve eq78097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78097
  have eq79938 : ∀ X0 : G, (τ (k (σ y) (σ y))) = (M.op X0 (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq402 (σ y) x
       have i₂ := eq69827
       grind)
    | exact superpose eq69827 eq402
    | exact resolve eq402 eq69827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79939 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (M.op X0 (τ (σ y))) = (k (τ (σ y)) X0) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq403 (σ y) X0
       have i₂ := eq69827
       grind)
    | exact superpose eq69827 eq403
    | (have j0 := eq403 (σ y) X0
       grind)
    | exact resolve eq403 eq69827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69827
  have eq79975 : ∀ X0 : G, (M.op X0 (τ (σ y))) = (k (τ (σ y)) X0) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq79939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79939
  have eq79999 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq79975 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq79975
    | exact resolve eq79975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79975
  have eq80000 : ∀ X0 : G, (M.op X0 y) = (τ (k (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq79938 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq79938
    | exact resolve eq79938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79938
  have eq80018 : ∀ X0 : G, (M.op X0 y) = (k y (τ (σ y))) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq80000 X0
       have i₂ := eq20 (σ y) y
       grind)
    | exact superpose eq20 eq80000
    | exact resolve eq80000 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80000
  have eq80030 : ∀ X0 : G, (k y y) = (M.op X0 y) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq80018 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq80018
    | exact resolve eq80018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80018
  have eq80156 : ∀ X0 : G, (k y y) = (k y X0) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq79999 X0
       have i₂ := eq80030 X0
       grind)
    | exact superpose eq80030 eq79999
    | exact resolve eq79999 eq80030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79999 eq80030
  have eq80196 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (k y y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq80156 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80156
  have eq80404 : ∀ X0 X1 : G, (τ (k (σ x) (σ x))) = (M.op X0 (τ (σ x))) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq402 (σ x) x
       have i₂ := eq80196 X0
       grind)
    | exact superpose eq80196 eq402
    | (have j1 := eq80196 X1
       grind)
    | exact resolve eq402 eq80196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq80405 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 (τ (σ x))) = (k (τ (σ x)) X0) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq403 (σ x) X0
       have i₂ := eq80196 X1
       grind)
    | exact superpose eq80196 eq403
    | (have j0 := eq403 (σ x) X0
       have j1 := eq80196 X1
       grind)
    | exact resolve eq403 eq80196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq80421 : ∀ X0 X1 : G, (k X0 (τ (k (σ x) (σ x)))) = X0 ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq69021 X0 (σ x)
       have i₂ := eq80196 X0
       grind)
    | exact superpose eq80196 eq69021
    | (have j1 := eq80196 X1
       grind)
    | exact resolve eq69021 eq80196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69021 eq80196
  have eq80441 : ∀ X0 X1 : G, (M.op X0 (τ (σ x))) = (k (τ (σ x)) X0) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have j0 := eq80405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80405
  have eq80454 : ∀ X0 X1 : G, (k X0 (k x (τ (σ x)))) = X0 ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80421 X0 X1
       have i₂ := eq20 (σ x) x
       grind)
    | exact superpose eq20 eq80421
    | (have j0 := eq80421 X0 X1
       grind)
    | exact resolve eq80421 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80421
  have eq80465 : ∀ X0 X1 : G, (M.op X0 x) = (k x X0) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80441 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80441
    | (have j0 := eq80441 X0 X1
       grind)
    | exact resolve eq80441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80441
  have eq80466 : ∀ X0 X1 : G, (M.op X0 x) = (τ (k (σ x) (σ x))) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80404 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80404
    | (have j0 := eq80404 X0 X1
       grind)
    | exact resolve eq80404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80404
  have eq80480 : ∀ X0 X1 : G, (k X0 (k x x)) = X0 ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80454 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80454
    | (have j0 := eq80454 X0 X1
       grind)
    | exact resolve eq80454 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80454
  have eq80484 : ∀ X0 X1 : G, (M.op X0 x) = (k x (τ (σ x))) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80466 X0 X1
       have i₂ := eq20 (σ x) x
       grind)
    | exact superpose eq20 eq80466
    | (have j0 := eq80466 X0 X1
       grind)
    | exact resolve eq80466 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq80466
  have eq80496 : ∀ X0 X1 : G, (M.op X0 x) = (k x x) ∨ (k y y) = (k y X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80484 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80484
    | (have j0 := eq80484 X0 X1
       grind)
    | exact resolve eq80484 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80484
  have eq80622 : ∀ X0 X1 X2 : G, (k x x) = (k x X0) ∨ (k y y) = (k y X1) ∨ (k y y) = (k y X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80465 X0 X1
       have i₂ := eq80496 X0 X2
       grind)
    | exact superpose eq80496 eq80465
    | (have j0 := eq80465 X0 X1
       have j1 := eq80496 X0 X1
       grind)
    | exact resolve eq80465 eq80496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80465 eq80496
  have eq80658 : ∀ X0 X1 : G, (k x x) = (k x X1) ∨ (k y y) = (k y X0) := by
    intro X0 X1
    first
    | (have j0 := eq80622 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80622
  have eq81913 : ∀ X0 X1 X2 X3 : G, (k X1 (k x X0)) = X1 ∨ (k y y) = (k y X2) ∨ (k y y) = (k y X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq80480 X1 X2
       have i₂ := eq80658 X3 X0
       grind)
    | (have i₁ := eq80480 X0 X1
       have i₂ := eq80658 X0 x
       grind)
    | exact superpose eq80658 eq80480
    | (have j0 := eq80480 X0 X2
       have j1 := eq80658 X2 X1
       grind)
    | exact resolve eq80480 eq80658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80480 eq80658
  have eq82123 : ∀ X0 X1 X2 : G, (k y y) = (k y X0) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq81913 X2 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81913
  have eq82627 : ∀ X1 X2 : G, y = (k y y) ∨ (k X1 (k x X2)) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq70969 x y
       have i₂ := eq82123 (k (k x x) (k x x)) X1 X2
       grind)
    | exact superpose eq82123 eq70969
    | (have j1 := eq82123 x X1 X2
       grind)
    | exact resolve eq70969 eq82123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82629 : ∀ X0 : G, y ≠ (k y y) ∨ y = (k y (k x X0)) := by
    intro X0
    first
    | (have j0 := eq82123 X0 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82661 : ∀ X0 X1 X2 X3 X4 : G, y = (k y X0) ∨ (k X1 (k x X2)) = X1 ∨ (k X3 (k x X4)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq82123 X0 X1 X2
       have i₂ := eq82627 X3 X4
       grind)
    | exact superpose eq82627 eq82123
    | (have j0 := eq82123 X0 X1 X2
       have j1 := eq82627 X1 X2
       grind)
    | exact resolve eq82123 eq82627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82123
  have eq82662 : ∀ X0 X1 X2 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq278 y X0
       have i₂ := eq82627 X1 X2
       grind)
    | exact superpose eq82627 eq278
    | (have j0 := eq278 y X0
       have j1 := eq82627 X1 X2
       grind)
    | (have r₁ := eq278 y X1
       have r₂ := eq82627 X1 X2
       grind)
    | (have r₁ := eq278 (k x X2) X1
       have r₂ := eq82627 (k x X2) X2
       grind)
    | exact resolve eq278 eq82627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82688 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ (k X0 (k x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 y y
       have i₂ := eq82627 X0 X1
       grind)
    | exact superpose eq82627 eq15
    | (have j1 := eq82627 X0 X1
       grind)
    | exact resolve eq15 eq82627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82698 : ∀ X0 X1 X2 : G, (k y X0) = (M.op X0 y) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq82662 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82662
  have eq82699 : ∀ X0 X1 X2 : G, y = (k y X2) ∨ (k X0 (k x X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq82661 X2 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82661
  have eq83410 : ∀ X0 X1 X2 : G, y ≠ y ∨ y = (k y (k x X0)) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82629 X0
       have i₂ := eq82627 X1 X2
       grind)
    | exact superpose eq82627 eq82629
    | (have j0 := eq82629 X0
       have j1 := eq82627 y X0
       grind)
    | (have r₁ := eq82629 X0
       have r₂ := eq82627 X1 X2
       grind)
    | exact resolve eq82629 eq82627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82627 eq82629
  have eq83413 : ∀ X0 X1 X2 : G, y = (k y (k x X0)) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq83410 X0 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83410
  have eq83414 : ∀ X0 : G, y = (k y (k x X0)) := by
    intro X0
    first
    | (have j0 := eq83413 X0 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83413
  have eq83489 : y = (k y x) := by
    first
    | (have i₁ := eq83414 (k (k x x) (k x x))
       have i₂ := eq70969 x x
       grind)
    | exact superpose eq70969 eq83414
    | exact resolve eq83414 eq70969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70969 eq83414
  have eq83530 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq83489
       grind)
    | exact superpose eq83489 eq15
    | exact resolve eq15 eq83489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83489
  have eq84337 : ∀ X0 X1 X2 : G, (σ y) = (k (σ y) (σ X0)) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq82699 X1 X2 X0
       grind)
    | exact superpose eq82699 eq15
    | (have j1 := eq82699 X1 X2 X2
       grind)
    | exact resolve eq15 eq82699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82699
  have eq111300 : ∀ X0 X1 X2 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq278 (σ y) X0
       have i₂ := eq82688 X1 X2
       grind)
    | exact superpose eq82688 eq278
    | (have j0 := eq278 (σ y) X0
       have j1 := eq82688 X1 X2
       grind)
    | (have r₁ := eq278 (σ y) X1
       have r₂ := eq82688 X0 X1
       grind)
    | (have r₁ := eq278 (k x X1) X1
       have r₂ := eq82688 (k x X1) X1
       grind)
    | exact resolve eq278 eq82688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq82688
  have eq111348 : ∀ X0 X1 X2 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (k X1 (k x X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq111300 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111300
  have eq201430 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (k X0 (k x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq111348 (σ x) X0 X1
       grind)
    | exact superpose eq111348 eq16
    | (have j1 := eq111348 X0 X0 X1
       grind)
    | exact resolve eq16 eq111348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111348
  have eq201440 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (k x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq201430 X0 X1
       have i₂ := eq83530
       grind)
    | exact superpose eq83530 eq201430
    | (have j0 := eq201430 X0 X1
       grind)
    | exact resolve eq201430 eq83530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83530 eq201430
  have eq201457 : ∀ X0 X1 X2 X3 : G, (σ y) ≠ (σ (k y x)) ∨ (k X0 (k x X1)) = X0 ∨ (k X2 (k x X3)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq201440 X0 X1
       have i₂ := eq82698 x X2 X3
       grind)
    | exact superpose eq82698 eq201440
    | (have j0 := eq201440 X0 X1
       have j1 := eq82698 X0 X0 X1
       grind)
    | exact resolve eq201440 eq82698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82698 eq201440
  have eq201493 : ∀ X0 X1 : G, (k X0 (k x X1)) = X0 ∨ (σ y) ≠ (σ (k y x)) := by
    intro X0 X1
    first
    | (have j0 := eq201457 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201457
  have eq201505 : ∀ X0 X1 : G, (σ y) ≠ (k (σ y) (σ x)) ∨ (k X0 (k x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq201493 X0 X1
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq201493
    | (have j0 := eq201493 X0 X1
       grind)
    | exact resolve eq201493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201493
  have eq201519 : ∀ X0 X1 : G, (k X0 (k x X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq201505 X0 X1
       have j1 := eq84337 X0 X0 X1
       grind)
    | (have r₁ := eq201505 X0 X1
       have r₂ := eq84337 x X1 x
       grind)
    | exact resolve eq201505 eq84337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84337 eq201505
  have eq202846 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq201519 X0 (k x x)
       have i₂ := eq201519 x x
       grind)
    | exact superpose eq201519 eq201519
    | exact resolve eq201519 eq201519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202951 : ∀ X0 : G, (k x x) = (k (k x x) X0) := by
    intro X0
    first
    | (have i₁ := eq2425 x x
       have i₂ := eq201519 (k x x) x
       grind)
    | exact superpose eq201519 eq2425
    | exact resolve eq2425 eq201519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq202964 : ∀ X0 X1 : G, (M.op X1 (k x X0)) = (k (k x X0) (k x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 (k x X1)
       have i₂ := eq201519 (k x X1) X1
       grind)
    | exact superpose eq201519 eq354
    | exact resolve eq354 eq201519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq202965 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (k x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq363 (k x X0) X1
       have i₂ := eq201519 (k x X0) X0
       grind)
    | exact superpose eq201519 eq363
    | exact resolve eq363 eq201519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203408 : ∀ X0 X1 : G, (k x X0) = (M.op X1 (k x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202964 X0 X1
       have i₂ := eq201519 (k x X0) X0
       grind)
    | exact superpose eq201519 eq202964
    | exact resolve eq202964 eq201519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201519 eq202964
  have eq206165 : ∀ X0 : G, x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq202951 X0
       have i₂ := eq202846 x
       grind)
    | exact superpose eq202846 eq202951
    | exact resolve eq202951 eq202846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202951
  have eq211145 : ∀ X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq202965 x X1
       have i₂ := eq206165 x
       grind)
    | exact superpose eq206165 eq202965
    | exact resolve eq202965 eq206165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202965
  have eq211162 : ∀ X1 : G, x = (M.op X1 x) := by
    intro X1
    first
    | (have i₁ := eq203408 x X1
       have i₂ := eq206165 x
       grind)
    | exact superpose eq206165 eq203408
    | exact resolve eq203408 eq206165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203408 eq206165
  have eq213393 : (M.op (σ x) (σ y)) ≠ (σ (k (k y y) (k y y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211145 y
       grind)
    | exact superpose eq211145 eq16
    | exact resolve eq16 eq211145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211145
  have eq214218 : (M.op (σ x) (σ y)) ≠ (k (σ (k y y)) (σ (k y y))) := by
    first
    | (have i₁ := eq213393
       have i₂ := eq15 (k y y) (k y y)
       grind)
    | exact superpose eq15 eq213393
    | exact resolve eq213393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213393
  have eq214430 : (M.op (σ x) (σ y)) ≠ (k (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq214218
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq214218
    | exact resolve eq214218 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214218
  have eq214650 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq202846 X0
       grind)
    | exact superpose eq202846 eq15
    | exact resolve eq15 eq202846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202846
  have eq216453 : ∀ X0 : G, (k X0 (k (σ x) (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq78298 X0 x x
       have i₂ := eq211162 x
       grind)
    | exact superpose eq211162 eq78298
    | exact resolve eq78298 eq211162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78298 eq211162
  have eq216492 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq216453 X0
       have i₂ := eq214650 x
       grind)
    | exact superpose eq214650 eq216453
    | exact resolve eq216453 eq214650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214650 eq216453
  have eq217535 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq363 (σ x) X0
       have i₂ := eq216492 (σ x)
       grind)
    | exact superpose eq216492 eq363
    | exact resolve eq363 eq216492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq216492
  have eq218030 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) ≠ (k (k (σ y) (σ y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq214430
       have i₂ := eq217535 (σ y)
       grind)
    | exact superpose eq217535 eq214430
    | (have r₁ := eq214430
       have r₂ := eq217535 (σ y)
       grind)
    | exact resolve eq214430 eq217535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214430 eq217535
  have eq218031 : False := by grind
  exact eq218031

/-- `Equation4515`: `x ◇ (y ◇ z) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_x_pxy_y_pxy_Equation4515 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4515 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4515.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X2) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
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
  clear eq36
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
  have eq175 : ∀ X0 : G, (M.op x (M.op X0 y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X1)) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X2) X3 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X1)) = (M.op X0 (M.op X3 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2 X3
       have i₂ := eq16 X0 X3 (M.op X1 X2)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op X0 (M.op (M.op X3 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq178 X0 X1 X2 X3
       have i₂ := eq16 X0 (M.op X3 X1) X2
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op X0 (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq179 X0 X1 X2 X3
       have i₂ := eq16 X3 X2 X1
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op (k X0 X1) X2) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 (M.op X0 X1) X2
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X0 X1) X2
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (k x y) ∨ x = (M.op y y) := by
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
  have eq187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq191 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (k X0 (σ y))) ∨ (M.op (σ y) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq176
    | (have j1 := eq28 X0 (σ y)
       grind)
    | exact resolve eq176 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq206 eq16
    | exact resolve eq16 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq217 x
       have i₂ := eq16 sF2 x sF4
       grind)
    | exact superpose eq16 eq217
    | exact resolve eq217 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq427 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq186
       grind)
    | exact superpose eq186 eq41
    | exact resolve eq41 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq428 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq427
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq427
    | exact resolve eq427 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq430 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq428
    | exact resolve eq428 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq430 eq187
    | exact resolve eq187 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq430
  have eq526 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq519
       have r₂ := eq27
       grind)
    | exact resolve eq519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq624 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X1 X1) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X2) X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq526 eq13
    | exact resolve eq13 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq630 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq28 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X1)) ≠ (M.op X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq16 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq627
  have eq636 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 (M.op X1 X1))) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq631 X0 X1 X2
       have i₂ := eq16 X0 X1 X1
       grind)
    | exact superpose eq16 eq631
    | (have j0 := eq631 X0 X1 X2
       grind)
    | (have r₁ := eq631 X0 X2 (M.op X0 X2)
       have r₂ := eq16 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq631 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq637 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq630 X0 X1
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq630
    | (have j0 := eq630 X0 X1
       grind)
    | (have r₁ := eq630 X0 X0
       have r₂ := eq633 X0
       grind)
    | exact resolve eq630 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq640 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) := by
    first
    | (have i₁ := eq634
       have i₂ := eq633 y
       grind)
    | exact superpose eq633 eq634
    | exact resolve eq634 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq643 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (k X1 X1) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq624 X0 X1 X2
       have i₂ := eq633 X1
       grind)
    | exact superpose eq633 eq624
    | (have j0 := eq624 X0 X1 X2
       grind)
    | exact resolve eq624 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq644 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 (k X1 X1))) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq636 X0 X1 X2
       have i₂ := eq633 X1
       grind)
    | exact superpose eq633 eq636
    | (have j0 := eq636 X0 X1 X2
       grind)
    | exact resolve eq636 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq653 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq653
    | (have j0 := eq653 X0
       grind)
    | exact resolve eq653 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq658 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq654 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq654
    | (have j0 := eq654 X0
       grind)
    | exact resolve eq654 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq660 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq658
    | (have j0 := eq658 X0
       grind)
    | exact resolve eq658 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq663 : (τ (σ x)) = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq640 eq116
    | exact resolve eq116 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq640
  have eq670 : x = (k y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq663
    | exact resolve eq663 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq671 : x = (k y y) := by grind
  clear eq670
  have eq678 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq41
    | exact resolve eq41 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq681 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq678
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq678
    | exact resolve eq678 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq684 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq681
    | exact resolve eq681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq1460 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq16
    | exact resolve eq16 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1469 : (M.op (M.op x y) y) = (M.op x (k y y)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq633 y
       grind)
    | exact superpose eq633 eq175
    | exact resolve eq175 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1476 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq176 sF3
       have i₂ := eq633 sF3
       grind)
    | exact superpose eq633 eq176
    | exact resolve eq176 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq684 eq1476
    | exact resolve eq1476 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1511 : (M.op (M.op x y) y) = (M.op x x) := by
    first
    | (have i₁ := eq1469
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq1469
    | exact resolve eq1469 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1530 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq1504
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq1504
    | exact resolve eq1504 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1537 : (k x x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1511
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq1511
    | exact resolve eq1511 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1841 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1530 eq176
    | exact resolve eq176 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (k (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq1530 eq16
    | exact resolve eq16 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1847 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1846 x
       have i₂ := eq1461 sF2 x
       grind)
    | exact superpose eq1461 eq1846
    | exact resolve eq1846 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1850 : (M.op (σ x) (k (σ x) (σ x))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1841
       have i₂ := eq633 sF4
       grind)
    | exact superpose eq633 eq1841
    | exact resolve eq1841 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1863 : (M.op (M.op x y) (M.op x y)) = (M.op x (k x x)) := by
    first
    | exact superpose eq1537 eq175
    | exact resolve eq175 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1864 : (k x x) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1537 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1867 : (M.op x y) = (k y y) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1864
       have i₂ := eq633 y
       grind)
    | exact superpose eq633 eq1864
    | exact resolve eq1864 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1864
  have eq1868 : (k (M.op x y) (M.op x y)) = (M.op x (k x x)) := by
    first
    | (have i₁ := eq1863
       have i₂ := eq633 sF0
       grind)
    | exact superpose eq633 eq1863
    | exact resolve eq1863 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863
  have eq1870 : (k x x) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1867
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq1867
    | exact resolve eq1867 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq1877 : ∀ X0 : G, (M.op (σ x) (M.op X0 (k (σ x) (σ x)))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq1850 eq16
    | exact resolve eq16 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1878 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq1877 x
       have i₂ := eq1461 sF4 x
       grind)
    | exact superpose eq1461 eq1877
    | exact resolve eq1877 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq1916 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X1) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1847 (M.op X0 x)
       have i₂ := eq16 X0 sF3 x
       grind)
    | exact superpose eq16 eq1847
    | exact resolve eq1847 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1924 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (M.op X0 (σ x)))) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq1847 eq180
    | exact resolve eq180 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1928 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (σ y)))) = (M.op (M.op (σ x) (M.op X0 (σ x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1847 eq16
    | exact resolve eq16 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1929 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (σ y)))) = (M.op (σ x) (M.op X1 (M.op X0 (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1928 X0 X1
       have i₂ := eq16 sF2 X1 (M.op X0 sF2)
       grind)
    | exact superpose eq16 eq1928
    | exact resolve eq1928 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1939 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X1))) = (M.op (σ x) (M.op X0 (M.op (σ x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1916 X0 x
       have i₂ := eq16 X0 sF2 x
       grind)
    | exact superpose eq16 eq1916
    | exact resolve eq1916 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1916
  have eq2036 : (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1850 eq1878
    | exact resolve eq1878 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq2623 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (σ x)))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq1847 eq1929
    | exact resolve eq1929 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1847 eq1929
  have eq2650 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (σ x)))) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq218 eq2623
    | exact resolve eq2623 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq2623
  have eq2962 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (σ x)))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq1939 eq1924
    | exact resolve eq1924 eq1939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924 eq1939
  have eq2967 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq2650 eq2962
    | exact resolve eq2962 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq2962
  have eq3120 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq684 eq184
    | (have j0 := eq184 (σ y) (σ y) x
       grind)
    | exact resolve eq184 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3228 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq3120 X0
       have i₂ := eq633 sF3
       grind)
    | exact superpose eq633 eq3120
    | (have j0 := eq3120 X0
       grind)
    | exact resolve eq3120 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3272 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ x) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq684 eq3228
    | (have j0 := eq3228 X0
       grind)
    | exact resolve eq3228 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3331 : (σ x) = (k (k (σ x) (σ x)) (σ x)) ∨ (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1850
       have i₂ := eq660 sF2
       grind)
    | exact superpose eq660 eq1850
    | (have j1 := eq660 (σ x)
       grind)
    | exact resolve eq1850 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3608 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq176 x
       have i₂ := eq185 sF2 sF3 x
       grind)
    | exact superpose eq185 eq176
    | (have j1 := eq185 (σ x) (σ y) X0
       grind)
    | exact resolve eq176 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3634 : (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2036
       have i₂ := eq185 sF4 sF4 sF2
       grind)
    | exact superpose eq185 eq2036
    | (have j1 := eq185 (σ x) (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq2036 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3637 : (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3634
       have i₂ := eq633 sF4
       grind)
    | exact superpose eq633 eq3634
    | exact resolve eq3634 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634
  have eq3662 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq26 eq3608
    | (have j0 := eq3608 X0
       grind)
    | exact resolve eq3608 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608
  have eq3789 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq3637
       have i₂ := eq633 sF4
       grind)
    | exact superpose eq633 eq3637
    | exact resolve eq3637 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3797 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq3662 X0
       have i₂ := eq633 X0
       grind)
    | exact superpose eq633 eq3662
    | (have j0 := eq3662 X0
       grind)
    | exact resolve eq3662 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3871 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq3789
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq3789
    | exact resolve eq3789 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq3875 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq26 eq3797
    | (have j0 := eq3797 X0
       grind)
    | exact resolve eq3797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797
  have eq4039 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq3272
    | (have j0 := eq3272 (σ x)
       grind)
    | exact resolve eq3272 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272
  have eq4073 : (k (σ x) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4039
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq4039
    | exact resolve eq4039 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4039
  have eq4136 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (k (σ x) (σ x)) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq4073 eq16
    | exact resolve eq16 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4073
  have eq4137 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq4136 x
       have i₂ := eq1461 sF2 x
       grind)
    | exact superpose eq1461 eq4136
    | exact resolve eq4136 eq1461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4567 : (k x x) ≠ (k y y) ∨ y = (k y y) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | exact superpose eq1537 eq637
    | (have j0 := eq637 y x
       grind)
    | exact resolve eq637 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq4589 : x ≠ (k x x) ∨ y = (k y y) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq4567
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq4567
    | exact resolve eq4567 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq4601 : x = y ∨ x ≠ (k x x) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq4589
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq4589
    | exact resolve eq4589 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589
  have eq4606 : y = (M.op x y) ∨ x ≠ (k x x) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | exact superpose eq1870 eq4601
    | exact resolve eq4601 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601
  have eq4609 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | exact superpose eq1870 eq4606
    | exact resolve eq4606 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4606
  have eq4722 : (k (σ x) (σ x)) ≠ (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq2036 eq643
    | exact resolve eq643 eq2036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq4724 : (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (k (σ x) (σ x)) ≠ (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq4722
       have i₂ := eq633 sF4
       grind)
    | exact superpose eq633 eq4722
    | exact resolve eq4722 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4722
  have eq4803 : (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (k (σ x) (σ x)) ≠ (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq3871 eq4724
    | exact resolve eq4724 eq3871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq4840 : (k (σ x) (σ x)) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1850 eq4803
    | exact resolve eq4803 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq4851 : (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have r₁ := eq4840
       have r₂ := eq3871
       grind)
    | exact resolve eq4840 eq3871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871 eq4840
  have eq5120 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4137 sF4
       have i₂ := eq633 sF4
       grind)
    | exact superpose eq633 eq4137
    | exact resolve eq4137 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq5173 : (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq206 eq5120
    | exact resolve eq5120 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq5120
  have eq10147 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1461 y X0
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq1461
    | exact resolve eq1461 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10151 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq684 eq1461
    | exact resolve eq1461 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10676 : (M.op x y) = (M.op y (k y y)) := by
    first
    | (have i₁ := eq10147 y
       have i₂ := eq633 y
       grind)
    | exact superpose eq633 eq10147
    | exact resolve eq10147 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10683 : (M.op x (M.op x y)) = (M.op y (k x x)) := by
    first
    | exact superpose eq1537 eq10147
    | exact resolve eq10147 eq1537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq10147
  have eq10718 : (M.op (M.op x y) x) = (M.op y (k x x)) := by
    first
    | exact superpose eq191 eq10683
    | exact resolve eq10683 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq10683
  have eq10722 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq10676
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq10676
    | exact resolve eq10676 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10676
  have eq10735 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq10722
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10722
    | exact resolve eq10722 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10722
  have eq10751 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10761 : (M.op x y) = (k y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq10751
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq10751
    | exact resolve eq10751 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10751
  have eq10797 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq10151 sF3
       have i₂ := eq633 sF3
       grind)
    | exact superpose eq633 eq10151
    | exact resolve eq10151 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10805 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1530 eq10151
    | exact resolve eq10151 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq10858 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq684 eq10797
    | exact resolve eq10797 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10797
  have eq10875 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10858
    | exact resolve eq10858 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10858
  have eq10908 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10875 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq10875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq10918 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10908
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq10908
    | exact resolve eq10908 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10908
  have eq10973 : ∀ X0 : G, (M.op (M.op (M.op x y) x) X0) = (M.op y (M.op X0 (k x x))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 (k x x)
       have i₂ := eq10718
       grind)
    | exact superpose eq10718 eq16
    | exact resolve eq16 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10982 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op y (M.op X0 (k x x))) := by
    intro X0
    first
    | (have i₁ := eq10973 x
       have i₂ := eq16 sF0 x x
       grind)
    | exact superpose eq16 eq10973
    | exact resolve eq10973 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10973
  have eq11249 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq10761
       grind)
    | exact superpose eq10761 eq40
    | exact resolve eq40 eq10761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10761
  have eq11251 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq11249
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11249
    | exact resolve eq11249 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11249
  have eq11253 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq20 eq11251
    | exact resolve eq11251 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11251
  have eq11275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq11253 eq10918
    | exact resolve eq10918 eq11253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10918 eq11253
  have eq11284 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | (have r₁ := eq11275
       have r₂ := eq27
       grind)
    | exact resolve eq11275 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11275
  have eq11360 : (τ (σ y)) = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq11284 eq98
    | exact resolve eq98 eq11284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11284
  have eq11412 : y = (k x x) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq11360
    | exact resolve eq11360 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11360
  have eq11413 : y = (k x x) := by grind
  clear eq11412
  have eq11430 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1868
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq1868
    | exact resolve eq1868 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11431 : y = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq1870
    | exact resolve eq1870 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq11440 : (M.op y y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq10718
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq10718
    | exact resolve eq10718 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11443 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq40
    | exact resolve eq40 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq11455 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11443
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11443
    | exact resolve eq11443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443
  have eq11457 : (k y y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11440
       have i₂ := eq633 y
       grind)
    | exact superpose eq633 eq11440
    | exact resolve eq11440 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11440
  have eq11462 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq11430
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11430
    | exact resolve eq11430 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11430
  have eq11465 : (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq11455
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11455
    | exact resolve eq11455 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11455
  have eq11467 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11457
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq11457
    | exact resolve eq11457 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11457
  have eq11471 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (k x x) = (k (M.op x y) y) := by
    first
    | exact superpose eq11462 eq4609
    | (have r₁ := eq4609
       have r₂ := eq11462
       grind)
    | exact resolve eq4609 eq11462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4609
  have eq11475 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11462 eq42
    | exact resolve eq42 eq11462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq11483 : y = (M.op x y) ∨ (k x x) = (k (M.op x y) y) := by grind
  clear eq11471
  have eq11486 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq11475
    | exact resolve eq11475 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11475
  have eq11490 : y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11483
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq11483
    | exact resolve eq11483 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483
  have eq11501 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11465 eq1850
    | exact resolve eq1850 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq11506 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11465 eq3331
    | exact resolve eq3331 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3331
  have eq11513 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11465 eq10805
    | exact resolve eq10805 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10805
  have eq11521 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11465 eq660
    | exact resolve eq660 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq11523 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq11465 eq1461
    | exact resolve eq1461 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq11528 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11521
    | exact resolve eq11521 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq11533 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11513
       have i₂ := eq633 sF3
       grind)
    | exact superpose eq633 eq11513
    | exact resolve eq11513 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11513
  have eq11542 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq11501
    | exact resolve eq11501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11501
  have eq11550 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq684 eq11533
    | exact resolve eq11533 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11533
  have eq11569 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq11467 eq16
    | exact resolve eq16 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11571 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) (M.op x y)) ∨ (M.op (M.op x y) (M.op x y)) = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq11467 eq185
    | (have j0 := eq185 X0 x (M.op x y)
       grind)
    | exact resolve eq185 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11573 : ∀ X0 : G, (k (M.op x y) (M.op x y)) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11467 eq643
    | exact resolve eq643 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11576 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 x) ∨ (M.op X0 x) = (k (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11462 eq11573
    | (have j0 := eq11573 X0
       grind)
    | exact resolve eq11573 eq11462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11573
  have eq11577 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 x) ∨ (M.op X0 x) = (k (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq11571 X0
       have i₂ := eq633 sF0
       grind)
    | exact superpose eq633 eq11571
    | (have j0 := eq11571 X0
       grind)
    | exact resolve eq11571 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11571
  have eq11586 : ∀ X0 : G, (M.op x y) = (M.op X0 x) ∨ (M.op X0 x) = (k (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq11462 eq11577
    | (have j0 := eq11577 X0
       grind)
    | exact resolve eq11577 eq11462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11577
  have eq11594 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq11586 X0
       have j1 := eq11576 X0
       grind)
    | (have r₁ := eq11586 X0
       have r₂ := eq11576 X0
       grind)
    | exact resolve eq11586 eq11576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11576 eq11586
  have eq11618 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq11542 eq4851
    | exact resolve eq4851 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11628 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq11550 eq11618
    | exact resolve eq11618 eq11550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11618
  have eq11654 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq11550 eq16
    | exact resolve eq16 eq11550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11700 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq11628 eq142
    | exact resolve eq142 eq11628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq11628
  have eq11703 : x = (k (τ (M.op (σ x) (σ y))) x) := by
    first
    | exact superpose eq30 eq11700
    | exact resolve eq11700 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11700
  have eq11708 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op (σ x) (σ y))) (M.op X0 x)) ∨ (τ (M.op (σ x) (σ y))) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq11703 eq184
    | (have j0 := eq184 (τ (M.op (σ x) (σ y))) x x
       grind)
    | exact resolve eq184 eq11703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq11703
  have eq11709 : ∀ X0 : G, (k x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x X0) = (M.op (τ (M.op (σ x) (σ y))) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq11708 X0
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq11708
    | (have j0 := eq11708 X0
       grind)
    | exact resolve eq11708 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11708
  have eq11712 : ∀ X0 : G, (M.op x X0) = (M.op (τ (M.op (σ x) (σ y))) (M.op X0 x)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq11709 X0
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq11709
    | (have j0 := eq11709 X0
       grind)
    | exact resolve eq11709 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709
  have eq12754 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (M.op (σ x) X1))) = (M.op (σ y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11523 (M.op X0 x)
       have i₂ := eq16 X0 sF2 x
       grind)
    | exact superpose eq16 eq11523
    | exact resolve eq11523 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11523
  have eq13046 : (k x x) = (M.op (M.op x y) (k x x)) := by
    first
    | (have i₁ := eq11569 x
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq11569
    | exact resolve eq11569 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13105 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq13046
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq13046
    | exact resolve eq13046 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13046
  have eq13175 : (k x x) = (k (k x x) (M.op x y)) := by
    first
    | (have i₁ := eq11594 x
       have i₂ := eq633 x
       grind)
    | exact superpose eq633 eq11594
    | exact resolve eq11594 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11594
  have eq13194 : y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq13175
       have i₂ := eq11413
       grind)
    | exact superpose eq11413 eq13175
    | exact resolve eq13175 eq11413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11413 eq13175
  have eq14006 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ x) (M.op X0 (M.op (M.op (σ x) (σ y)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11654 (M.op X0 x)
       have i₂ := eq16 X0 sF4 x
       grind)
    | exact superpose eq16 eq11654
    | exact resolve eq11654 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14024 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) = (M.op (σ x) (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq11654 eq2967
    | exact resolve eq2967 eq11654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2967
  have eq14042 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ x) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq11654 eq16
    | exact resolve eq16 eq11654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14051 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 X0)) = (M.op (σ x) (M.op X1 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq14042 x X1
       have i₂ := eq16 sF2 X1 x
       grind)
    | exact superpose eq16 eq14042
    | exact resolve eq14042 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14042
  have eq14067 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | (have i₁ := eq14024 X0
       have i₂ := eq180 sF2 (M.op X0 sF4) sF4 sF2
       grind)
    | (have i₁ := eq14024 X0
       have i₂ := eq180 sF2 sF4 (M.op X0 sF4) sF2
       grind)
    | exact superpose eq180 eq14024
    | exact resolve eq14024 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq14024
  have eq14094 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq12754 eq14067
    | exact resolve eq14067 eq12754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12754 eq14067
  have eq14109 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ x) (M.op (σ x) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq14006 eq14094
    | exact resolve eq14094 eq14006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14006 eq14094
  have eq14118 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq14051 eq14109
    | exact resolve eq14109 eq14051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14051 eq14109
  have eq14336 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11506 eq4851
    | exact resolve eq4851 eq11506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4851
  have eq14338 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11506 eq5173
    | exact resolve eq5173 eq11506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173 eq11506
  have eq14356 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11654 eq14338
    | exact resolve eq14338 eq11654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11654 eq14338
  have eq14358 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq14336
    | exact resolve eq14336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14336
  have eq14365 : (k (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14356
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq14356
    | exact resolve eq14356 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14356
  have eq14367 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11528 eq14358
    | exact resolve eq14358 eq11528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11528 eq14358
  have eq14369 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14365
       have i₂ := eq633 sF3
       grind)
    | exact superpose eq633 eq14365
    | exact resolve eq14365 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14365
  have eq14371 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq684 eq14369
    | exact resolve eq14369 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14369
  have eq14373 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq11465 eq14371
    | exact resolve eq14371 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14371
  have eq14374 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq14373
  have eq14444 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq14367
  have eq14446 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq14444
       have r₂ := eq14374
       grind)
    | exact resolve eq14444 eq14374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14374 eq14444
  have eq14466 : (τ (σ x)) = (k y (τ (σ x))) := by
    first
    | exact superpose eq14446 eq108
    | exact resolve eq108 eq14446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14446
  have eq14473 : x = (k y x) := by
    first
    | exact superpose eq30 eq14466
    | exact resolve eq14466 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14466
  have eq18765 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14118 eq10151
    | exact resolve eq10151 eq14118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10151 eq14118
  have eq18828 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11550 eq18765
    | exact resolve eq18765 eq11550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11550 eq18765
  have eq18908 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq176 eq18828
    | exact resolve eq18828 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq18828
  have eq19032 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) ∨ (M.op X0 (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq18908 eq185
    | (have j0 := eq185 X0 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq185 eq18908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq19034 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq18908 eq643
    | exact resolve eq643 eq18908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq18908
  have eq19037 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq11542 eq19034
    | (have j0 := eq19034 X0
       grind)
    | exact resolve eq19034 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19034
  have eq19038 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq19032 X0
       have i₂ := eq633 sF4
       grind)
    | exact superpose eq633 eq19032
    | (have j0 := eq19032 X0
       grind)
    | exact resolve eq19032 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19032
  have eq19049 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq11542 eq19038
    | (have j0 := eq19038 X0
       grind)
    | exact resolve eq19038 eq11542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11542 eq19038
  have eq19057 : ∀ X0 : G, (M.op X0 (σ x)) = (k (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq19049 X0
       have j1 := eq19037 X0
       grind)
    | (have r₁ := eq19049 X0
       have r₂ := eq19037 X0
       grind)
    | exact resolve eq19049 eq19037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19037 eq19049
  have eq19297 : (k (σ x) (σ x)) = (k (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19057 sF2
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq19057
    | exact resolve eq19057 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19057
  have eq19325 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11465 eq19297
    | exact resolve eq19297 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19297
  have eq19336 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq19325 eq108
    | exact resolve eq108 eq19325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq19325
  have eq19339 : y = (k y (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq32 eq19336
    | exact resolve eq19336 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19336
  have eq34820 : ∀ X0 : G, (M.op X0 (M.op y x)) ≠ (M.op (M.op x y) (M.op y x)) ∨ (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq644 y x X0
       have i₂ := eq10982 y
       grind)
    | exact superpose eq10982 eq644
    | (have j0 := eq644 y x X0
       grind)
    | (have r₁ := eq644 y x (M.op x y)
       have r₂ := eq10982 y
       grind)
    | exact resolve eq644 eq10982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq10982
  have eq34859 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op y x)) ∨ (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
    intro X0
    first
    | exact superpose eq11569 eq34820
    | (have j0 := eq34820 X0
       grind)
    | exact resolve eq34820 eq11569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11569 eq34820
  have eq34901 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq34859 X0
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq34859
    | (have j0 := eq34859 X0
       grind)
    | exact resolve eq34859 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34859
  have eq34939 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op y x)) = (k X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq34901 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34901
    | (have j0 := eq34901 X0
       grind)
    | exact resolve eq34901 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34901
  have eq34972 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq34939 X0
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq34939
    | (have j0 := eq34939 X0
       grind)
    | exact resolve eq34939 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34939
  have eq65740 : y ≠ (k y y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq13105 eq1460
    | exact resolve eq1460 eq13105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460 eq13105
  have eq65784 : x ≠ y ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq65740
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq65740
    | exact resolve eq65740 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65740
  have eq65830 : x ≠ (M.op x y) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq11490 eq65784
    | exact resolve eq65784 eq11490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11490 eq65784
  have eq65867 : y = (k (M.op x y) y) := by
    first
    | (have r₁ := eq65830
       have r₂ := eq11431
       grind)
    | exact resolve eq65830 eq11431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11431 eq65830
  have eq65904 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq65867 eq38
    | exact resolve eq38 eq65867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq65867
  have eq65917 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq65904
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65904
    | exact resolve eq65904 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65904
  have eq65935 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq65917 eq204
    | (have j0 := eq204 (σ (M.op x y))
       grind)
    | exact resolve eq204 eq65917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq65917
  have eq65949 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq65935
    | exact resolve eq65935 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq65935
  have eq65959 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq65949
       have i₂ := eq633 sF3
       grind)
    | exact superpose eq633 eq65949
    | exact resolve eq65949 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65949
  have eq65962 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq684 eq65959
    | exact resolve eq65959 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq65959
  have eq66041 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq65962 eq3875
    | (have j0 := eq3875 (σ (M.op x y))
       grind)
    | exact resolve eq3875 eq65962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3875 eq65962
  have eq66083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11486 eq66041
    | exact resolve eq66041 eq11486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11486 eq66041
  have eq66097 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq66083
       have r₂ := eq27
       grind)
    | exact resolve eq66083 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66083
  have eq87827 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq11712 y
       have i₂ := eq10735
       grind)
    | exact superpose eq10735 eq11712
    | exact resolve eq11712 eq10735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10735 eq11712
  have eq87930 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq87827
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87827
    | exact resolve eq87827 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq87827
  have eq88020 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq87930 eq34972
    | (have r₁ := eq34972 (τ (M.op (σ x) (σ y)))
       have r₂ := eq87930
       grind)
    | exact resolve eq34972 eq87930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34972 eq87930
  have eq88036 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq88020
  have eq88219 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq88036 eq35
    | exact resolve eq35 eq88036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq88036
  have eq88230 : (σ (M.op x y)) = (k (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq88219
    | exact resolve eq88219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88219
  have eq88260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq88230 eq66097
    | exact resolve eq66097 eq88230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66097 eq88230
  have eq88274 : y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq88260
       have r₂ := eq27
       grind)
    | exact resolve eq88260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88260
  have eq88304 : y = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq88274 eq19339
    | exact resolve eq19339 eq88274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19339 eq88274
  have eq88368 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq88304
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq88304
    | exact resolve eq88304 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq88304
  have eq88932 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq88368 eq117
    | exact resolve eq117 eq88368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq88368
  have eq89100 : (k y x) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq115 eq88932
    | exact resolve eq88932 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq88932
  have eq89151 : y = (k y x) ∨ x = y := by
    first
    | exact superpose eq13194 eq89100
    | exact resolve eq89100 eq13194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13194 eq89100
  have eq89158 : x = y ∨ x = y := by
    first
    | (have i₁ := eq89151
       have i₂ := eq14473
       grind)
    | exact superpose eq14473 eq89151
    | exact resolve eq89151 eq14473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14473 eq89151
  have eq89159 : x = y := by grind
  clear eq89158
  have eq89166 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq89159
       grind)
    | exact superpose eq89159 eq24
    | exact resolve eq24 eq89159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq89202 : (M.op (M.op x y) x) = (M.op x (k x x)) := by
    first
    | (have i₁ := eq10718
       have i₂ := eq89159
       grind)
    | exact superpose eq89159 eq10718
    | exact resolve eq10718 eq89159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10718 eq89159
  have eq89305 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq89202
       have i₂ := eq1868
       grind)
    | exact superpose eq1868 eq89202
    | exact resolve eq89202 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868 eq89202
  have eq89323 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq89166
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89166
    | exact resolve eq89166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89166
  have eq89334 : x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11467 eq89305
    | exact resolve eq89305 eq11467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11467 eq89305
  have eq89348 : x = (M.op x y) := by
    first
    | exact superpose eq11462 eq89334
    | exact resolve eq89334 eq11462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11462 eq89334
  have eq89444 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq89323 eq10875
    | exact resolve eq10875 eq89323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq89551 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq89444
       have i₂ := eq633 sF2
       grind)
    | exact superpose eq633 eq89444
    | exact resolve eq89444 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq89444
  have eq89625 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11465 eq89551
    | exact resolve eq89551 eq11465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11465 eq89551
  have eq89671 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq89323 eq89625
    | exact resolve eq89625 eq89323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89323 eq89625
  have eq89701 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq89348
       grind)
    | exact superpose eq89348 eq22
    | exact resolve eq22 eq89348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq89348
  have eq90005 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq89671 eq27
    | exact resolve eq27 eq89671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq89671
  have eq90678 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq89701 eq20
    | exact resolve eq20 eq89701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq89701
  have eq90745 : False := by grind
  exact eq90745

/-- `Equation4522`: `x ◇ (y ◇ z) = (x ◇ w) ◇ u`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_y_pyx_Equation4522 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4522 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4522.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X4) := by
    intro X0 X1 X2 X3 X4
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq55 : ∀ X0 X1 X2 X5 X6 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X5) X6) := by
    intro X0 X1 X2 X5 X6
    first
    | (have i₁ := eq14 X0 x x X5 X6
       have i₂ := eq14 X0 x x X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 x X0 X1 y X2
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 X1 y X2
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y) X2
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x x
       have i₂ := eq14 X0 X3 X4 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq95 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq96
  have eq101 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq125
  have eq129 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq128
  have eq168 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq59 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 x y X0
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X4 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq59 x x X4
       have i₂ := eq14 x x x X0 X1
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq238 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq221 eq129
    | exact resolve eq129 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq60 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | (have j0 := eq60 x y X0
       grind)
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
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
    grind
  clear eq310
  have eq379 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq60
    | exact resolve eq60 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq381 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (M.op X1 X2)) = (M.op (σ (M.op X0 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) X1 X2 (σ X0) X3
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq251 eq379
    | exact resolve eq379 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq392 : ∀ X0 X1 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq221 eq226
    | exact resolve eq226 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq422 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y) X2 X0 X1
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq450 : ∀ X0 X1 : G, (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq251 eq422
    | exact resolve eq422 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq473 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 x y X1 X2
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 X0 X1 X2 x y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq814 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq473 X0 x x
       have i₂ := eq14 X0 x x X1 X2
       grind)
    | exact superpose eq14 eq473
    | (have j1 := eq14 X0 x y X1 X2
       grind)
    | exact resolve eq473 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq74 eq312
    | exact resolve eq312 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1171 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq168 eq312
    | exact resolve eq312 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1192 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (M.op (τ X0) (τ X0))
       have i₂ := eq312 X0
       grind)
    | exact superpose eq312 eq45
    | exact resolve eq45 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq1194 : ∀ X0 : G, (M.op X0 (M.op x y)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq1192 X0
       have i₂ := eq814 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq814 eq1192
    | exact resolve eq1192 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1195 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1171
       have i₂ := eq814 sF0 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq814 eq1171
    | exact resolve eq1171 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq1197 : (M.op (σ x) (M.op x y)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq450 eq1169
    | exact resolve eq1169 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq1169
  have eq1198 : ∀ X0 : G, (M.op X0 (M.op x y)) = (σ (M.op (τ X0) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1194 X0
       have i₂ := eq814 (τ X0) (τ X0) (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq814 eq1194
    | exact resolve eq1194 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1199 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq1195
       have i₂ := eq814 sF1 sF1 (M.op sF1 sF1)
       grind)
    | exact superpose eq814 eq1195
    | exact resolve eq1195 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1201 : (σ (M.op x (M.op x y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq1197
       have i₂ := eq392 x (M.op x x)
       grind)
    | exact superpose eq392 eq1197
    | exact resolve eq1197 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq1197
  have eq1202 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq129 eq1199
    | exact resolve eq1199 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1199
  have eq1203 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq238 eq1201
    | exact resolve eq1201 eq238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238 eq1201
  have eq1218 : (M.op (σ x) (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq1202 eq1203
    | exact resolve eq1203 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1203
  have eq1219 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq83
  have eq1284 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1219 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1219
    | (have j0 := eq1219 X0 x
       grind)
    | exact resolve eq1219 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1402 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1198 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1198
    | exact resolve eq1198 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : ∀ X0 : G, (M.op (τ X0) (M.op x y)) = (τ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1198 eq16
    | exact resolve eq16 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1559 : ∀ X0 X1 : G, (τ (M.op X0 (M.op x y))) = (M.op (τ (M.op X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1415 eq814
    | exact resolve eq814 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1415
  have eq1780 : ∀ X0 : G, (M.op (σ x) (σ (M.op X0 X0))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1218 eq385
    | exact resolve eq385 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq1797 : (M.op (σ (M.op x y)) (M.op x y)) = (M.op (σ x) (σ (M.op (σ x) (M.op x y)))) := by
    first
    | exact superpose eq251 eq1780
    | exact resolve eq1780 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1825 : (M.op (σ (M.op x y)) (M.op x y)) = (M.op (σ x) (σ (M.op (σ (M.op x y)) (M.op x y)))) := by
    first
    | exact superpose eq1218 eq1797
    | exact resolve eq1797 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq2408 : ∀ X0 X3 : G, (M.op (σ (M.op X0 X0)) X3) = (M.op (σ X0) (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq381 X0 x x X3
       have i₂ := eq473 (σ X0) x x
       grind)
    | (have i₁ := eq381 X0 x y X3
       have i₂ := eq473 (σ X0) x x
       grind)
    | exact superpose eq473 eq381
    | (have j0 := eq381 X0 x y X3
       grind)
    | exact resolve eq381 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq473
  have eq2409 : ∀ X0 X3 : G, (M.op (σ (M.op X0 X0)) X3) = (σ (M.op X0 (M.op x y))) := by
    intro X0 X3
    first
    | exact superpose eq1402 eq2408
    | exact resolve eq2408 eq1402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq2408
  have eq2456 : ∀ X0 X1 X2 X4 : G, (M.op (σ (M.op X0 X0)) (M.op X1 X2)) = (M.op (σ (M.op X0 (M.op x y))) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (σ (M.op X0 X0)) X1 X2 x X4
       have i₂ := eq2409 X0 x
       grind)
    | exact superpose eq2409 eq14
    | exact resolve eq14 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2496 : ∀ X0 X4 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) X4) := by
    intro X0 X4
    first
    | (have i₁ := eq2456 X0 x x X4
       have i₂ := eq2409 X0 (M.op x x)
       grind)
    | exact superpose eq2409 eq2456
    | exact resolve eq2456 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409 eq2456
  have eq8455 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1284 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1284
    | (have j0 := eq1284 y
       grind)
    | exact resolve eq1284 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq8526 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8455
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq8455
    | exact resolve eq8455 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8455
  have eq8569 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq8526
    | exact resolve eq8526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8526
  have eq8594 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8569
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq8569
    | exact resolve eq8569 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8569
  have eq8610 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq8594
    | exact resolve eq8594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8594
  have eq23347 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23347
    | exact resolve eq23347 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23347
  have eq23361 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq23348
       have r₂ := eq28
       grind)
    | exact resolve eq23348 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23348
  have eq23366 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23361
    | exact resolve eq23361 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23361
  have eq23378 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (k (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23366 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq23366
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23366
       grind)
    | exact resolve eq12 eq23366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23366
  have eq148293 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq23378
    | (have j0 := eq23378 (σ x)
       grind)
    | (have r₁ := eq23378 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq23378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23378
  have eq148295 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq148293
  have eq148296 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq148295
  have eq148338 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq148296 eq110
    | exact resolve eq110 eq148296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq148296
  have eq148357 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq148338
  have eq148379 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq148357
       grind)
    | exact superpose eq148357 eq101
    | exact resolve eq101 eq148357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq148393 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (k y X0) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq148357
       grind)
    | exact superpose eq148357 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq148357
       grind)
    | exact resolve eq12 eq148357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148357
  have eq148456 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq148379
    | exact resolve eq148379 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148379
  have eq2118900 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq148393 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq148393
    | (have j0 := eq148393 x
       grind)
    | (have r₁ := eq148393 x
       have r₂ := eq19
       grind)
    | exact resolve eq148393 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148393
  have eq2118955 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq2118900
  have eq2118956 : x = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq2118955
  have eq2122928 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq2118956
       grind)
    | exact superpose eq2118956 eq95
    | exact resolve eq95 eq2118956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq2118956
  have eq2123102 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2122928
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2122928
    | exact resolve eq2122928 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122928
  have eq2123406 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2123102 eq8610
    | exact resolve eq8610 eq2123102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8610 eq2123102
  have eq2123502 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2123406
  have eq2123635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2123502 eq148456
    | exact resolve eq148456 eq2123502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148456 eq2123502
  have eq2123942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2123635
  have eq2124032 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2123942
       have r₂ := eq28
       grind)
    | exact resolve eq2123942 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123942
  have eq2127258 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op (σ x) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2124032 eq251
    | exact resolve eq251 eq2124032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq2127592 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq1218 eq2127258
    | exact resolve eq2127258 eq1218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218 eq2127258
  have eq2149461 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27 eq2127592
    | (have j0 := eq2127592 (σ y)
       grind)
    | exact resolve eq2127592 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2150426 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2149461 eq1825
    | exact resolve eq1825 eq2149461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq2149461
  have eq2168494 : (σ x) = (M.op (σ x) (σ (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2124032 eq2150426
    | exact resolve eq2150426 eq2124032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124032 eq2150426
  have eq2168570 : (σ x) = (M.op (σ x) (σ (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2168494
  have eq2191304 : (σ x) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2168570 eq2127592
    | exact resolve eq2127592 eq2168570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127592 eq2168570
  have eq2191331 : (σ x) = (M.op (σ (M.op x y)) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq2191304
  have eq2191760 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2191331 eq1559
    | exact resolve eq1559 eq2191331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559 eq2191331
  have eq2192200 : ∀ X0 : G, x = (M.op x X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq29 eq2191760
    | exact resolve eq2191760 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191760
  have eq2204207 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2192200 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2192200
    | (have j0 := eq2192200 y
       grind)
    | exact resolve eq2192200 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192200
  have eq2205513 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2204207 eq30
    | exact resolve eq30 eq2204207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2204207
  have eq2205721 : x = y ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq2205513
    | exact resolve eq2205513 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205513
  have eq2205722 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2205721
  have eq2205791 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2205722 eq29
    | exact resolve eq29 eq2205722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2205722
  have eq2206614 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq2205791
    | exact resolve eq2205791 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2205791
  have eq2206615 : x = (M.op x y) ∨ x = y := by grind
  clear eq2206614
  have eq2206754 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2206615 eq21
    | exact resolve eq21 eq2206615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2206793 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2206615 eq221
    | exact resolve eq221 eq2206615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq2206615
  have eq2208495 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2206754
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2206754
    | exact resolve eq2206754 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206754
  have eq2208547 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2208495 eq27
    | exact resolve eq27 eq2208495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208495
  have eq2210133 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2206793 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2206793
    | (have j0 := eq2206793 y
       grind)
    | exact resolve eq2206793 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2211455 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2206793 X0
       have i₂ := eq2210133
       grind)
    | exact superpose eq2210133 eq2206793
    | exact resolve eq2206793 eq2210133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206793 eq2210133
  have eq2211563 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2211455 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211455
  have eq2212454 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2496 x x
       have i₂ := eq2211563 sF0
       grind)
    | exact superpose eq2211563 eq2496
    | exact resolve eq2496 eq2211563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496 eq2211563
  have eq2212819 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq21 eq2212454
    | (have j0 := eq2212454 X0
       grind)
    | exact resolve eq2212454 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212454
  have eq2214170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2212819 eq2208547
    | exact resolve eq2208547 eq2212819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208547 eq2212819
  have eq2214627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2214170
  have eq2215216 : x = y := by
    first
    | (have r₁ := eq2214627
       have r₂ := eq28
       grind)
    | exact resolve eq2214627 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214627
  have eq2215275 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2215216
       grind)
    | exact superpose eq2215216 eq19
    | exact resolve eq19 eq2215216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2215276 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2215216
       grind)
    | exact superpose eq2215216 eq25
    | exact resolve eq25 eq2215216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2215216
  have eq2215671 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2215276
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2215276
    | exact resolve eq2215276 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2215276
  have eq2215713 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2215671 eq27
    | exact resolve eq27 eq2215671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2215671
  have eq2216458 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2215713 eq74
    | exact resolve eq74 eq2215713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq2215713
  have eq2216653 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2216458
       have i₂ := eq2215275
       grind)
    | exact superpose eq2215275 eq2216458
    | exact resolve eq2216458 eq2215275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215275 eq2216458
  have eq2216735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2216653 eq15
    | exact resolve eq15 eq2216653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216653
  have eq2217536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2216735
    | exact resolve eq2216735 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2216735
  have eq2217771 : False := by grind
  exact eq2217771

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq43
    | exact resolve eq43 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq49
    | exact resolve eq49 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq74
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq81 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
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
  have eq95 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq106 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq106
    | exact resolve eq106 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq112 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq110
    | exact resolve eq110 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq110
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq120
    | exact resolve eq120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq151 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq16
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1625 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq81 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1671 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1673 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq1676 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1673 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1673
    | (have j0 := eq1673 X0 X1
       grind)
    | exact resolve eq1673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq37179 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq108
    | (have j0 := eq108 X0
       grind)
    | exact resolve eq108 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq37263 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37179 eq13
    | (have j0 := eq13 (σ y) (σ X0)
       have j1 := eq37179 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ X0)
       have r₂ := eq37179 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq37179 y
       grind)
    | exact resolve eq13 eq37179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37319 : ∀ X0 : G, (σ (k y X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37320 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37179
  have eq37336 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37263 X0
       have j1 := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq37263 X0
       have r₂ := eq13 (σ y) (σ X0)
       grind)
    | (have r₁ := eq37263 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq37263 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37263
  have eq37362 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq37336 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq37336
    | (have j0 := eq37336 X0
       grind)
    | exact resolve eq37336 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37336
  have eq37377 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k y X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq37362
    | (have j0 := eq37362 X0
       grind)
    | exact resolve eq37362 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq37362
  have eq38337 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq179
    | (have j0 := eq179 X0
       grind)
    | exact resolve eq179 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq38493 : ∀ X0 : G, (σ (k X0 x)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq38337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38337
  have eq60791 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1671 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq1671
    | (have j0 := eq1671 X0 X1
       grind)
    | exact resolve eq1671 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq60792 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60791 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq60791
    | (have j0 := eq60791 X0 X1
       grind)
    | (have r₁ := eq60791 X0 X0
       have r₂ := eq77 X0
       grind)
    | exact resolve eq60791 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60791
  have eq60793 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq60792 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq60792
    | (have j0 := eq60792 X0 X1
       grind)
    | exact resolve eq60792 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60792
  have eq80854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1676 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq1676
    | (have j0 := eq1676 X0 X1
       grind)
    | exact resolve eq1676 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq80855 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80854 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq80854
    | (have j0 := eq80854 X0 X1
       grind)
    | exact resolve eq80854 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80854
  have eq80856 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80855 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq80855
    | (have j0 := eq80855 X0 X1
       grind)
    | exact resolve eq80855 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80855
  have eq80857 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80856 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq80856
    | (have j0 := eq80856 X0 X1
       grind)
    | exact resolve eq80856 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80856
  have eq80858 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq80857 X0 X1
       have j1 := eq60793 X0 X1
       grind)
    | (have r₁ := eq80857 X0 X1
       have r₂ := eq60793 X0 X1
       grind)
    | (have r₁ := eq80857 X1 X0
       have r₂ := eq60793 X0 X1
       grind)
    | exact resolve eq80857 eq60793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60793 eq80857
  have eq81135 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq80858 X0 X1
       grind)
    | exact superpose eq80858 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq80858 X1 X0
       grind)
    | exact resolve eq12 eq80858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80858
  have eq81238 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81135 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq81135
    | (have j0 := eq81135 X0 X1
       grind)
    | exact resolve eq81135 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81135
  have eq81291 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81238 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq81238
    | (have j0 := eq81238 X0 X1
       grind)
    | exact resolve eq81238 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81238
  have eq81292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81291
  have eq81334 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81292 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq81292
    | (have j0 := eq81292 X0 X1
       grind)
    | exact resolve eq81292 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq81292
  have eq81357 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81334 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq81334
    | (have j0 := eq81334 X0 X1
       grind)
    | exact resolve eq81334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81334
  have eq81358 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq81357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81357
  have eq121351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121352 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq121351
    | exact resolve eq121351 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121351
  have eq121363 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq121352
       have r₂ := eq27
       grind)
    | exact resolve eq121352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121352
  have eq121367 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq121363
    | exact resolve eq121363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121363
  have eq121369 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq121367
    | exact resolve eq121367 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121367
  have eq121381 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq121369 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq121369
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq121369
       grind)
    | exact resolve eq13 eq121369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121369
  have eq188788 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq121381
    | (have j0 := eq121381 (σ x)
       grind)
    | (have r₁ := eq121381 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq121381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121381
  have eq188794 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq188788
  have eq188979 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq188794 eq119
    | exact resolve eq119 eq188794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188794
  have eq189005 : (M.op x x) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq75 eq188979
    | exact resolve eq188979 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq188979
  have eq189929 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq189005
       grind)
    | exact superpose eq189005 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq189005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189005
  have eq189930 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq189929
  have eq189933 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq189930
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189930
    | exact resolve eq189930 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189930
  have eq189934 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq189933
  have eq189948 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq189934
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq189934
    | exact resolve eq189934 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189934
  have eq189949 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq189948
  have eq189961 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq189949 eq95
    | (have r₁ := eq95
       have r₂ := eq189949
       grind)
    | exact resolve eq95 eq189949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq190169 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq189961
  have eq229454 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq190169 eq119
    | exact resolve eq119 eq190169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq190169
  have eq229485 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq151 eq229454
    | exact resolve eq229454 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq229454
  have eq229491 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq229485
       have r₂ := eq94
       grind)
    | exact resolve eq229485 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229485
  have eq229507 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq229491
       grind)
    | exact superpose eq229491 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq229491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229491
  have eq229508 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq229507
  have eq229513 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq229508
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq229508
    | exact resolve eq229508 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229508
  have eq229514 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq229513
  have eq229528 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq229514
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq229514
    | exact resolve eq229514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229514
  have eq229570 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq229528 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq229528
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq229528
       grind)
    | exact resolve eq13 eq229528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229528
  have eq598690 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq229570
    | (have j0 := eq229570 (σ x)
       grind)
    | (have r₁ := eq229570 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq229570 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229570
  have eq598706 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq598690
  have eq599020 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq598706 eq123
    | exact resolve eq123 eq598706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq598706
  have eq599051 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq599020
  have eq599090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq599051 eq189949
    | exact resolve eq189949 eq599051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189949 eq599051
  have eq599463 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq599090
  have eq599629 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq599463
       have r₂ := eq27
       grind)
    | exact resolve eq599463 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599463
  have eq599791 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq599629
       grind)
    | exact superpose eq599629 eq112
    | exact resolve eq112 eq599629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599809 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq599629
       grind)
    | exact superpose eq599629 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq599629
       grind)
    | exact resolve eq13 eq599629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599629
  have eq600128 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq599791
    | exact resolve eq599791 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599791
  have eq1488719 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq599809 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq599809
    | (have j0 := eq599809 x
       grind)
    | (have r₁ := eq599809 x
       have r₂ := eq18
       grind)
    | exact resolve eq599809 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599809
  have eq1488740 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1488719
  have eq1489063 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq37319 x
       have i₂ := eq1488740
       grind)
    | exact superpose eq1488740 eq37319
    | (have j0 := eq37319 x
       grind)
    | exact resolve eq37319 eq1488740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37319
  have eq1489071 : (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1489063
  have eq1489079 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1489071
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1489071
    | exact resolve eq1489071 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489071
  have eq1489103 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1489079
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq1489079
    | exact resolve eq1489079 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489079
  have eq1489114 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1489103
    | exact resolve eq1489103 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489103
  have eq1489122 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1489114
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1489114
    | exact resolve eq1489114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489114
  have eq1489128 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1489122
    | exact resolve eq1489122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489122
  have eq1932873 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq81358 y x
       have i₂ := eq1488740
       grind)
    | exact superpose eq1488740 eq81358
    | (have j0 := eq81358 y x
       grind)
    | exact resolve eq81358 eq1488740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81358 eq1488740
  have eq1933315 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1932873
  have eq1933605 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1933315
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq1933315
    | exact resolve eq1933315 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933315
  have eq1934127 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1933605
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq1933605
    | exact resolve eq1933605 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933605
  have eq1934577 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1934127
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq1934127
    | exact resolve eq1934127 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934127
  have eq1934984 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1934577
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1934577
    | exact resolve eq1934577 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934577
  have eq1935317 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1934984
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1934984
    | exact resolve eq1934984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1934984
  have eq1935497 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq1935317
    | exact resolve eq1935317 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935317
  have eq2814153 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1935497
  have eq2814461 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2814153
       have r₂ := eq1489128
       grind)
    | exact resolve eq2814153 eq1489128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489128 eq2814153
  have eq2816332 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2814461 eq600128
    | exact resolve eq600128 eq2814461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600128 eq2814461
  have eq2817337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2816332
  have eq2817589 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2817337
       have r₂ := eq27
       grind)
    | exact resolve eq2817337 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817337
  have eq2817722 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq2817589
       grind)
    | exact superpose eq2817589 eq76
    | exact resolve eq76 eq2817589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2817723 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq2817589
       grind)
    | exact superpose eq2817589 eq94
    | (have r₁ := eq94
       have r₂ := eq2817589
       grind)
    | exact resolve eq94 eq2817589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq2818273 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq2817723
  have eq2818659 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq2817722
    | exact resolve eq2817722 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817722
  have eq2951788 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq38493 y
       have i₂ := eq2818273
       grind)
    | exact superpose eq2818273 eq38493
    | (have j0 := eq38493 y
       grind)
    | exact resolve eq38493 eq2818273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38493
  have eq2951799 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq37377 x
       have i₂ := eq2818273
       grind)
    | exact superpose eq2818273 eq37377
    | (have j0 := eq37377 x
       grind)
    | exact resolve eq37377 eq2818273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37377 eq2818273
  have eq2951806 : (σ (M.op y y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq2951788
  have eq2951815 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq2951799
       have r₂ := eq112
       grind)
    | exact resolve eq2951799 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951799
  have eq2951824 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951806
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2951806
    | exact resolve eq2951806 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951806
  have eq2951848 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951815
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq2951815
    | exact resolve eq2951815 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951815
  have eq2951857 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951824
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq2951824
    | exact resolve eq2951824 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951824
  have eq2951865 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951848
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq2951848
    | exact resolve eq2951848 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951848
  have eq2951874 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq2951857
    | exact resolve eq2951857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951857
  have eq2951883 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2818659 eq2951865
    | exact resolve eq2951865 eq2818659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951865
  have eq2951892 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951874
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2951874
    | exact resolve eq2951874 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2951874
  have eq2951898 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951883
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2951883
    | exact resolve eq2951883 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951883
  have eq2951907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2818659 eq2951892
    | exact resolve eq2951892 eq2818659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951892
  have eq2951911 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2951898
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq2951898
    | exact resolve eq2951898 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951898
  have eq2951920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq2951907
    | exact resolve eq2951907 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951907
  have eq2951924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2818659 eq2951911
    | exact resolve eq2951911 eq2818659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951911
  have eq2951933 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq2951920
       have r₂ := eq27
       grind)
    | exact resolve eq2951920 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951920
  have eq2951936 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq2951924
    | exact resolve eq2951924 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951924
  have eq2951947 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq2951936
       have r₂ := eq27
       grind)
    | exact resolve eq2951936 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951936
  have eq2953655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2951947 eq2951933
    | exact resolve eq2951933 eq2951947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2951933 eq2951947
  have eq2954507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq2953655
  have eq2954830 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq2954507
       have r₂ := eq27
       grind)
    | exact resolve eq2954507 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954507
  have eq2955044 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq2954830
       grind)
    | exact superpose eq2954830 eq112
    | exact resolve eq112 eq2954830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq2955158 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq2954830
       grind)
    | exact superpose eq2954830 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2954830
       grind)
    | exact resolve eq13 eq2954830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954830
  have eq2956115 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq2955044
    | exact resolve eq2955044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955044
  have eq3578367 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq2955158 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2955158
    | (have j0 := eq2955158 x
       grind)
    | (have r₁ := eq2955158 x
       have r₂ := eq18
       grind)
    | exact resolve eq2955158 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2955158
  have eq3578384 : (M.op x x) = (k y x) := by grind
  clear eq3578367
  have eq3578388 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq3578384
       have i₂ := eq2817589
       grind)
    | exact superpose eq2817589 eq3578384
    | exact resolve eq3578384 eq2817589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817589 eq3578384
  have eq3578924 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37320 x
       have i₂ := eq3578388
       grind)
    | exact superpose eq3578388 eq37320
    | (have j0 := eq37320 x
       grind)
    | exact resolve eq37320 eq3578388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37320 eq3578388
  have eq3578968 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2956115 eq3578924
    | (have r₁ := eq3578924
       have r₂ := eq2956115
       grind)
    | exact resolve eq3578924 eq2956115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578924
  have eq3579017 : (σ (M.op x x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3578968
       have r₂ := eq20
       grind)
    | exact resolve eq3578968 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3578968
  have eq3579043 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3579017
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3579017
    | exact resolve eq3579017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579017
  have eq3579061 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3579043
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq3579043
    | exact resolve eq3579043 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq3579043
  have eq3579068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2818659 eq3579061
    | exact resolve eq3579061 eq2818659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818659 eq3579061
  have eq3579074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3579068
    | exact resolve eq3579068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579068
  have eq3579081 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3579074
       have r₂ := eq27
       grind)
    | exact resolve eq3579074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3579074
  have eq3579086 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3579081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3579081
    | exact resolve eq3579081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3579081
  have eq3579091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2956115 eq3579086
    | exact resolve eq3579086 eq2956115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956115 eq3579086
  have eq3579096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3579091
    | exact resolve eq3579091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3579091
  have eq3579101 : False := by grind
  exact eq3579101

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq54 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq10
    | exact resolve eq10 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63 x
       grind)
    | exact superpose eq63 eq43
    | exact resolve eq43 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq69 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq63 sF2
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x y
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq89
    | exact resolve eq89 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq99 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24
  have eq101 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq74 sF3 (σ X0)
       grind)
    | exact superpose eq74 eq36
    | (have j1 := eq74 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq103 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq63 sF3
       grind)
    | exact superpose eq63 eq99
    | exact resolve eq99 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq105 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq103
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq103
    | exact resolve eq103 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq103
  have eq112 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq16
    | exact resolve eq16 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq119 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq120 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq16
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq371 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq658 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 X1
       have i₂ := eq74 (σ X0) X1
       grind)
    | exact superpose eq74 eq371
    | (have j1 := eq74 (σ X0) X1
       grind)
    | exact resolve eq371 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq684 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq658
  have eq695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq92 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq695
    | exact resolve eq695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq699 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq696
       have r₂ := eq27
       grind)
    | exact resolve eq696 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq701 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq699
    | exact resolve eq699 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq703 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq701 eq120
    | (have r₁ := eq120
       have r₂ := eq701
       grind)
    | exact resolve eq120 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq704 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq701 eq61
    | (have r₁ := eq61
       have r₂ := eq701
       grind)
    | exact resolve eq61 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq701
  have eq712 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq704
  have eq713 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq703
  have eq729 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq712 eq112
    | exact resolve eq112 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq712
  have eq848 : (M.op y y) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq713 eq127
    | exact resolve eq127 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq713
  have eq1280 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq848 eq729
    | exact resolve eq729 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq848
  have eq1298 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1280
  have eq3770 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ X0)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq101 eq13
    | (have j0 := eq13 (σ X0) (σ y)
       have j1 := eq101 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ y)
       have r₂ := eq101 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq101 y
       grind)
    | exact resolve eq13 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq3772 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3770 X0
       have j1 := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3770 X0
       have r₂ := eq13 (σ X0) (σ y)
       grind)
    | (have r₁ := eq3770 y
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq3770 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770
  have eq3783 : ∀ X0 : G, (σ (k y X0)) ≠ (M.op (σ y) (σ y)) ∨ (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq40 eq3772
    | (have j0 := eq3772 X0
       grind)
    | exact resolve eq3772 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3772
  have eq56252 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3783 x
       have i₂ := eq1298
       grind)
    | exact superpose eq1298 eq3783
    | (have j0 := eq3783 x
       grind)
    | exact resolve eq3783 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298 eq3783
  have eq56312 : (σ (k x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq56252
       have r₂ := eq105
       grind)
    | exact resolve eq56252 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq56252
  have eq56343 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq56312
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq56312
    | exact resolve eq56312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56312
  have eq56358 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq56343
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq56343
    | exact resolve eq56343 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq56343
  have eq56368 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq56358
    | exact resolve eq56358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56358
  have eq56369 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq56368
  have eq56381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq56369 eq92
    | exact resolve eq92 eq56369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq56369
  have eq56402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq56381
  have eq56406 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq56402
       have r₂ := eq27
       grind)
    | exact resolve eq56402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56402
  have eq56411 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq56406
       grind)
    | exact superpose eq56406 eq69
    | exact resolve eq69 eq56406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56413 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq56406
       grind)
    | exact superpose eq56406 eq119
    | (have r₁ := eq119
       have r₂ := eq56406
       grind)
    | exact resolve eq119 eq56406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq56406
  have eq56435 : (M.op y x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq56413
  have eq56448 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq56411
    | exact resolve eq56411 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56411
  have eq57790 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq56435
       grind)
    | exact superpose eq56435 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq56435
       grind)
    | exact resolve eq13 eq56435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56435
  have eq134813 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq684 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq684
    | (have j0 := eq684 x X0
       grind)
    | exact resolve eq684 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq684
  have eq135048 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq134813 X0
       have i₂ := eq250 X0
       grind)
    | exact superpose eq250 eq134813
    | (have j0 := eq134813 X0
       grind)
    | exact resolve eq134813 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq134813
  have eq135108 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq135048 X0
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq135048
    | (have j0 := eq135048 X0
       grind)
    | exact resolve eq135048 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq135048
  have eq135145 : ∀ X0 : G, (τ (k (σ x) X0)) = (τ (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq56448 eq135108
    | (have j0 := eq135108 X0
       grind)
    | exact resolve eq135108 eq56448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56448 eq135108
  have eq135314 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135145 eq54
    | (have j1 := eq135145 (σ y)
       grind)
    | exact resolve eq54 eq135145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq135145
  have eq135681 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq135314
    | exact resolve eq135314 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135314
  have eq135688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq135681
    | exact resolve eq135681 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq135681
  have eq135691 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq135688
       have r₂ := eq27
       grind)
    | exact resolve eq135688 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135688
  have eq590357 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq57790 X0
       have i₂ := eq135691
       grind)
    | exact superpose eq135691 eq57790
    | (have j0 := eq57790 X0
       grind)
    | exact resolve eq57790 eq135691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57790
  have eq590366 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq590357 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590357
  have eq590369 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq590366
       have i₂ := eq135691
       grind)
    | exact superpose eq135691 eq590366
    | exact resolve eq590366 eq135691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135691 eq590366
  have eq590372 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq590369
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq590369
    | exact resolve eq590369 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq590369
  have eq590373 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq590372
  have eq590397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq590373 eq15
    | exact resolve eq15 eq590373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590373
  have eq590854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq590397
    | exact resolve eq590397 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq590397
  have eq590865 : False := by grind
  exact eq590865

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq22 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq17
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq31
    | exact resolve eq31 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq69
    | exact resolve eq69 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq94 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq511 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq488 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq488
    | (have j0 := eq488 X0 X1
       grind)
    | exact resolve eq488 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq676 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq511 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq7382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq484 X0 X1
       grind)
    | exact superpose eq484 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq484 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq484 X0 X1
       grind)
    | exact resolve eq13 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7416 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq484 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq7418 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7382
  have eq7441 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq7418 X0 X1
       have j1 := eq7416 X0 X1
       grind)
    | (have r₁ := eq7418 X0 X1
       have r₂ := eq7416 X0 X1
       grind)
    | exact resolve eq7418 eq7416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7416 eq7418
  have eq7728 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq676 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq676
    | (have j0 := eq676 (τ X0) (τ X1)
       grind)
    | exact resolve eq676 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7806 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7728 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7728
    | (have j0 := eq7728 X0 X1
       grind)
    | exact resolve eq7728 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7728
  have eq7849 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7806 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7806
    | (have j0 := eq7806 X0 X1
       grind)
    | exact resolve eq7806 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7806
  have eq7885 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7849 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7849
    | (have j0 := eq7849 X0 X1
       grind)
    | exact resolve eq7849 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7849
  have eq7915 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7885 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7885
    | (have j0 := eq7885 X0 X1
       grind)
    | exact resolve eq7885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7885
  have eq7939 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7915 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq7915
    | (have j0 := eq7915 X0 X1
       grind)
    | exact resolve eq7915 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915
  have eq7956 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7939 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq7939
    | (have j0 := eq7939 X0 X1
       grind)
    | exact resolve eq7939 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq7969 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7956 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7956
    | (have j0 := eq7956 X0 X1
       grind)
    | exact resolve eq7956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7956
  have eq7982 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7969 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7969
    | (have j0 := eq7969 X0 X1
       grind)
    | exact resolve eq7969 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7969
  have eq8035 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7982 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq7982
    | (have j0 := eq7982 (τ X0) (τ X1)
       grind)
    | exact resolve eq7982 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7982
  have eq8084 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (M.op X0 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8035 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq8035
    | (have j0 := eq8035 X0 X1
       grind)
    | exact resolve eq8035 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq8035
  have eq9015 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7441 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7441
    | exact resolve eq7441 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9040 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (τ X0) = (k (τ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq7441 X0 X1
       grind)
    | exact superpose eq7441 eq22
    | (have j1 := eq7441 X0 X1
       grind)
    | exact resolve eq22 eq7441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7441
  have eq9127 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9015 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9015
    | (have j0 := eq9015 X0 X1
       grind)
    | exact resolve eq9015 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9015
  have eq9218 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq9127 X1 X0
       grind)
    | exact superpose eq9127 eq11
    | (have j1 := eq9127 X1 X0
       grind)
    | exact resolve eq11 eq9127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9127
  have eq9348 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9218 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq9218
    | (have j0 := eq9218 X0 X1
       grind)
    | exact resolve eq9218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9218
  have eq9404 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq9348 X0 (τ X1)
       grind)
    | exact superpose eq9348 eq18
    | (have j1 := eq9348 X0 (τ X1)
       grind)
    | exact resolve eq18 eq9348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9348
  have eq10065 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9404 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9404
    | exact resolve eq9404 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9404
  have eq10135 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10065 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10065
    | (have j0 := eq10065 X0 X1
       grind)
    | exact resolve eq10065 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10065
  have eq23232 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9040 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9040
    | (have j0 := eq9040 X1 (τ X0)
       grind)
    | exact resolve eq9040 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9040
  have eq23355 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X1) = (k (τ X1) (τ X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23232 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq23232
    | (have j0 := eq23232 X0 X1
       grind)
    | exact resolve eq23232 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23232
  have eq23356 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23355 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq23355
    | (have j0 := eq23355 X0 X1
       grind)
    | exact resolve eq23355 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23355
  have eq23431 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq23356 X1 X0
       grind)
    | exact superpose eq23356 eq11
    | (have j1 := eq23356 X1 X0
       grind)
    | exact resolve eq11 eq23356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23516 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq23356 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23356
  have eq23572 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23431 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq23431
    | (have j0 := eq23431 X0 X1
       grind)
    | exact resolve eq23431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23431
  have eq23755 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23572 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq23572
    | (have j0 := eq23572 (σ X0) (σ X1)
       grind)
    | exact resolve eq23572 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23572
  have eq24018 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23755 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq23755
    | (have j0 := eq23755 X0 X1
       grind)
    | exact resolve eq23755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23755
  have eq24046 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24018 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq24018
    | (have j0 := eq24018 X0 X1
       grind)
    | exact resolve eq24018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24018
  have eq24062 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24046 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq24046
    | (have j0 := eq24046 X0 X1
       grind)
    | exact resolve eq24046 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq24046
  have eq34400 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24062 x y
       grind)
    | exact superpose eq24062 eq16
    | (have j1 := eq24062 x y
       grind)
    | exact resolve eq16 eq24062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34493 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k X0 X1) = X0 ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24062 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24062
  have eq34575 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34400
       have i₂ := eq10135 y x
       grind)
    | exact superpose eq10135 eq34400
    | (have j1 := eq10135 y x
       grind)
    | (have r₁ := eq34400
       have r₂ := eq10135 y x
       grind)
    | exact resolve eq34400 eq10135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10135 eq34400
  have eq34578 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq34575
  have eq34579 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by grind
  clear eq34578
  have eq34589 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq34579
       grind)
    | exact superpose eq34579 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq34579
       grind)
    | exact resolve eq12 eq34579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34579
  have eq34598 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ x = (k x y) := by grind
  clear eq34589
  have eq34625 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34598
       grind)
    | exact superpose eq34598 eq16
    | exact resolve eq16 eq34598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34627 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq94 x (σ y)
       have i₂ := eq34598
       grind)
    | exact superpose eq34598 eq94
    | (have j0 := eq94 x (σ y)
       grind)
    | (have r₁ := eq94 x (σ y)
       have r₂ := eq34598
       grind)
    | exact resolve eq94 eq34598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34598
  have eq34650 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ x = (k x y) := by grind
  clear eq34627
  have eq34658 : x = (k x y) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq34650
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq34650
    | exact resolve eq34650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34650
  have eq34686 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34658
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq34658
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq34658 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34658
  have eq34711 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq34686
  have eq34738 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq34711
       grind)
    | exact superpose eq34711 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq34711
       grind)
    | exact resolve eq13 eq34711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34747 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq34711
  have eq34750 : x = (M.op x x) ∨ x = (k x y) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq34738
  have eq34752 : (M.op x y) = (M.op x x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq34750
       have r₂ := eq34747
       grind)
    | exact resolve eq34750 eq34747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34747 eq34750
  have eq34789 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq34752
       grind)
    | exact superpose eq34752 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq34752
       grind)
    | exact resolve eq12 eq34752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34752
  have eq34798 : (k x y) = (M.op x x) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by grind
  clear eq34789
  have eq34801 : x = (k x y) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq34798
       have r₂ := eq34625
       grind)
    | exact resolve eq34798 eq34625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34625 eq34798
  have eq34804 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34801
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq34801
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq34801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34824 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by grind
  clear eq34801
  have eq34829 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq34804
  have eq34861 : (τ x) ≠ (τ x) ∨ (τ (k x y)) = (τ x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq23516 x y
       have i₂ := eq34829
       grind)
    | exact superpose eq34829 eq23516
    | (have j0 := eq23516 x y
       grind)
    | exact resolve eq23516 eq34829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23516
  have eq34862 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  have eq34863 : (τ (k x y)) = (τ x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq34861
  have eq34866 : (M.op x y) = (M.op x x) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have r₁ := eq34863
       have r₂ := eq34862
       grind)
    | exact resolve eq34863 eq34862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34863
  have eq34903 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq34866
       grind)
    | exact superpose eq34866 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq34866
       grind)
    | exact resolve eq12 eq34866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34911 : (k x y) = (M.op x x) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq34903
  have eq36395 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq34493 x y
       have i₂ := eq34911
       grind)
    | exact superpose eq34911 eq34493
    | (have j0 := eq34493 x y
       grind)
    | exact resolve eq34493 eq34911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34493 eq34911
  have eq36431 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq36395
  have eq36796 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36431
       grind)
    | exact superpose eq36431 eq16
    | exact resolve eq16 eq36431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36431
  have eq36854 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (τ (k x y)) = (τ x) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq36796
       have i₂ := eq34866
       grind)
    | exact superpose eq34866 eq36796
    | exact resolve eq36796 eq34866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34866 eq36796
  have eq36873 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq36854
  have eq36874 : x = (M.op x x) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq36873
  have eq36891 : x ≠ x ∨ x = (k x y) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq34824
       have i₂ := eq36874
       grind)
    | exact superpose eq36874 eq34824
    | (have r₁ := eq34824
       have r₂ := eq36874
       grind)
    | exact resolve eq34824 eq36874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34824
  have eq36997 : x = (k x y) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq36891
  have eq37131 : (τ x) ≠ (τ x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq8084 x y
       have i₂ := eq36997
       grind)
    | exact superpose eq36997 eq8084
    | (have j0 := eq8084 x y
       grind)
    | (have r₁ := eq8084 x y
       have r₂ := eq36997
       grind)
    | exact resolve eq8084 eq36997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36997
  have eq37136 : (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq37131
  have eq37141 : (τ x) = (M.op (τ x) (τ y)) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) := by
    first
    | (have j1 := eq8084 x y
       grind)
    | (have r₁ := eq37136
       have r₂ := eq8084 x y
       grind)
    | exact resolve eq37136 eq8084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8084 eq37136
  have eq38041 : (τ (M.op x x)) ≠ (τ x) ∨ (τ (M.op x x)) = (k (τ x) (τ y)) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) := by
    first
    | (have i₁ := eq103 x (τ y)
       have i₂ := eq37141
       grind)
    | exact superpose eq37141 eq103
    | (have j0 := eq103 x (τ y)
       grind)
    | (have r₁ := eq103 x (τ y)
       have r₂ := eq37141
       grind)
    | exact resolve eq103 eq37141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37141
  have eq38075 : (τ (M.op x x)) ≠ (τ x) ∨ (τ (M.op x x)) = (k (τ x) (τ y)) := by
    first
    | (have j1 := eq103 x (τ y)
       grind)
    | (have r₁ := eq38041
       have r₂ := eq103 x (τ y)
       grind)
    | exact resolve eq38041 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq38041
  have eq38080 : (τ (M.op x x)) ≠ (τ x) ∨ (τ (k x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq38075
       have i₂ := eq31 y x
       grind)
    | exact superpose eq31 eq38075
    | exact resolve eq38075 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq38075
  have eq38083 : (τ x) ≠ (τ x) ∨ (τ (k x y)) = (τ x) ∨ (τ (k x y)) = (τ x) := by
    first
    | (have i₁ := eq38080
       have i₂ := eq36874
       grind)
    | exact superpose eq36874 eq38080
    | exact resolve eq38080 eq36874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36874 eq38080
  have eq38086 : (τ x) ≠ (τ x) ∨ (τ (k x y)) = (τ x) := by grind
  clear eq38083
  have eq38087 : (τ (k x y)) = (τ x) := by grind
  clear eq38086
  have eq38104 : (k x y) = (σ (τ x)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq38087
       grind)
    | exact superpose eq38087 eq11
    | exact resolve eq11 eq38087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38087
  have eq38250 : x = (k x y) := by
    first
    | (have i₁ := eq38104
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq38104
    | exact resolve eq38104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38104
  have eq38265 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq676 x y
       have i₂ := eq38250
       grind)
    | exact superpose eq38250 eq676
    | (have j0 := eq676 x y
       grind)
    | exact resolve eq676 eq38250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq38283 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq38265
  have eq40504 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq38283
       grind)
    | exact superpose eq38283 eq16
    | exact resolve eq16 eq38283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40529 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq38283
  have eq40559 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq40504
       have i₂ := eq34829
       grind)
    | exact superpose eq34829 eq40504
    | exact resolve eq40504 eq34829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34829
  have eq40580 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq40559
  have eq40605 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq94 x (σ y)
       have i₂ := eq40580
       grind)
    | exact superpose eq40580 eq94
    | (have j0 := eq94 x (σ y)
       grind)
    | (have r₁ := eq94 x (σ y)
       have r₂ := eq40580
       grind)
    | exact resolve eq94 eq40580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40580
  have eq40630 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq40605
  have eq40638 : (σ (k x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq40630
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq40630
    | exact resolve eq40630 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40630
  have eq40646 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40638
       have i₂ := eq38250
       grind)
    | exact superpose eq38250 eq40638
    | exact resolve eq40638 eq38250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40638
  have eq40673 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq40646
       grind)
    | exact superpose eq40646 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq40646
       grind)
    | exact resolve eq12 eq40646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40646
  have eq40683 : (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq40673
  have eq40686 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40683
       have i₂ := eq38250
       grind)
    | exact superpose eq38250 eq40683
    | exact resolve eq40683 eq38250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40683
  have eq40695 : x ≠ x ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq34862
       have i₂ := eq40686
       grind)
    | exact superpose eq40686 eq34862
    | (have r₁ := eq34862
       have r₂ := eq40686
       grind)
    | exact resolve eq34862 eq40686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40686
  have eq40817 : x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq40695
  have eq40909 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40504
       have i₂ := eq40817
       grind)
    | exact superpose eq40817 eq40504
    | exact resolve eq40504 eq40817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40504 eq40817
  have eq40930 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq40909
  have eq40934 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq40930
       have r₂ := eq40529
       grind)
    | exact resolve eq40930 eq40529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40930
  have eq40947 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq94 x (σ y)
       have i₂ := eq40934
       grind)
    | exact superpose eq40934 eq94
    | (have j0 := eq94 x (σ y)
       grind)
    | (have r₁ := eq94 x (σ y)
       have r₂ := eq40934
       grind)
    | exact resolve eq94 eq40934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq40934
  have eq40972 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq40947
  have eq40980 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40972
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq40972
    | exact resolve eq40972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40972
  have eq40988 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40980
       have i₂ := eq38250
       grind)
    | exact superpose eq38250 eq40980
    | exact resolve eq40980 eq38250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38250 eq40980
  have eq40996 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40529
       have i₂ := eq40988
       grind)
    | exact superpose eq40988 eq40529
    | (have r₁ := eq40529
       have r₂ := eq40988
       grind)
    | exact resolve eq40529 eq40988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40529
  have eq41015 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq40988
       grind)
    | exact superpose eq40988 eq10
    | exact resolve eq10 eq40988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40988
  have eq41141 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq40996
  have eq41213 : x = (M.op x x) := by
    first
    | (have i₁ := eq41015
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq41015
    | exact resolve eq41015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41015
  have eq41318 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34862
       have i₂ := eq41213
       grind)
    | exact superpose eq41213 eq34862
    | (have r₁ := eq34862
       have r₂ := eq41213
       grind)
    | exact resolve eq34862 eq41213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34862 eq41213
  have eq41440 : x = (M.op x y) := by grind
  clear eq41318
  have eq42007 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41141
       grind)
    | exact superpose eq41141 eq16
    | exact resolve eq16 eq41141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41141
  have eq42060 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq42007
       have i₂ := eq41440
       grind)
    | exact superpose eq41440 eq42007
    | exact resolve eq42007 eq41440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41440 eq42007
  have eq42061 : False := by grind
  exact eq42061

/-- `Equation72`: `x = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pxy_Equation72 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law72 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law72.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq35 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq14
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq47 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq57 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
    first
    | (have i₁ := eq54
       have i₂ := eq48 sF2
       grind)
    | exact superpose eq48 eq54
    | exact resolve eq54 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq57
       have i₂ := eq48 x
       grind)
    | exact superpose eq48 eq57
    | exact resolve eq57 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq58
       grind)
    | exact superpose eq58 eq16
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq55
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq55
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39
    | (have j0 := eq39 y
       grind)
    | exact resolve eq39 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq101 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq48 sF3
       grind)
    | exact superpose eq48 eq97
    | exact resolve eq97 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq102 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq48 y
       grind)
    | exact superpose eq48 eq101
    | exact resolve eq101 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq101
  have eq3468 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq14
    | exact resolve eq14 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3470 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq35
    | exact resolve eq35 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq36
  have eq12406 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3468 X1 X2
       have i₂ := eq3468 X1 X0
       grind)
    | exact superpose eq3468 eq3468
    | exact resolve eq3468 eq3468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12426 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3470 X1
       have i₂ := eq3468 X1 X0
       grind)
    | exact superpose eq3468 eq3470
    | exact resolve eq3470 eq3468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq12508 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq12426 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12426
    | (have j0 := eq12426 x y
       grind)
    | exact resolve eq12426 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12559 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq12508 eq12406
    | exact resolve eq12406 eq12508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12508
  have eq13237 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq12559 x
       have i₂ := eq12406 x sF0 x
       grind)
    | (have i₁ := eq12559 x
       have i₂ := eq12406 X0 sF0 x
       grind)
    | exact superpose eq12406 eq12559
    | exact resolve eq12559 eq12406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12406 eq12559
  have eq16853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq16853
    | exact resolve eq16853 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16853
  have eq16865 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq16854
       have r₂ := eq28
       grind)
    | exact resolve eq16854 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16854
  have eq16869 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq16865
    | exact resolve eq16865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16865
  have eq16871 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16869 eq47
    | (have r₁ := eq47
       have r₂ := eq16869
       grind)
    | exact resolve eq47 eq16869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq16869
  have eq16912 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq16871
  have eq17182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16912 eq88
    | exact resolve eq88 eq16912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq16912
  have eq17192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq17182
  have eq17195 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq17192
       have r₂ := eq28
       grind)
    | exact resolve eq17192 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17192
  have eq17201 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17195 eq75
    | exact resolve eq75 eq17195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17195
  have eq17261 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq30 eq17201
    | exact resolve eq17201 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17201
  have eq17262 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq17261
  have eq17552 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq58
       have i₂ := eq17262
       grind)
    | exact superpose eq17262 eq58
    | exact resolve eq58 eq17262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17562 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op x y))) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 x X0
       have i₂ := eq17262
       grind)
    | exact superpose eq17262 eq14
    | exact resolve eq14 eq17262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17262
  have eq17603 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq17552
    | exact resolve eq17552 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17552
  have eq17760 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17562 eq13237
    | exact resolve eq13237 eq17562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13237 eq17562
  have eq18699 : y = (M.op y (M.op y (M.op x x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12426 y y
       have i₂ := eq17760
       grind)
    | exact superpose eq17760 eq12426
    | exact resolve eq12426 eq17760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12426 eq17760
  have eq18704 : y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq18699
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq18699
    | exact resolve eq18699 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18699
  have eq18838 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq58
       have i₂ := eq18704
       grind)
    | exact superpose eq18704 eq58
    | exact resolve eq58 eq18704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq18870 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3468 x x
       have i₂ := eq18704
       grind)
    | exact superpose eq18704 eq3468
    | exact resolve eq3468 eq18704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18704
  have eq18882 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq18870
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18870
    | exact resolve eq18870 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18870
  have eq18900 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq18838
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18838
    | exact resolve eq18838 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18838
  have eq19147 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq102
       have i₂ := eq18882
       grind)
    | exact superpose eq18882 eq102
    | exact resolve eq102 eq18882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq18882
  have eq19208 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq19147
    | exact resolve eq19147 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19147
  have eq19329 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq18900 eq3468
    | exact resolve eq3468 eq18900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3468 eq18900
  have eq19341 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq19329
    | exact resolve eq19329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19329
  have eq20427 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq19341 eq19208
    | exact resolve eq19208 eq19341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19208 eq19341
  have eq20460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq20427
  have eq20471 : x = y := by
    first
    | (have r₁ := eq20460
       have r₂ := eq28
       grind)
    | exact resolve eq20460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20460
  have eq20473 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20471
       grind)
    | exact superpose eq20471 eq19
    | exact resolve eq19 eq20471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20474 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20471
       grind)
    | exact superpose eq20471 eq25
    | exact resolve eq25 eq20471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq20626 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20474
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20474
    | exact resolve eq20474 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20474
  have eq21066 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20626 eq27
    | exact resolve eq27 eq20626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20626
  have eq21344 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq21066 eq75
    | exact resolve eq75 eq21066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq21353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21066 eq17603
    | exact resolve eq17603 eq21066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17603 eq21066
  have eq21394 : y = (M.op x x) := by
    first
    | (have r₁ := eq21353
       have r₂ := eq28
       grind)
    | exact resolve eq21353 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21353
  have eq21402 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21344
       have i₂ := eq20473
       grind)
    | exact superpose eq20473 eq21344
    | exact resolve eq21344 eq20473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21344
  have eq21407 : y = (M.op x y) := by
    first
    | (have i₁ := eq21394
       have i₂ := eq20473
       grind)
    | exact superpose eq20473 eq21394
    | exact resolve eq21394 eq20473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20473 eq21394
  have eq21414 : x = (M.op x y) := by
    first
    | (have i₁ := eq21407
       have i₂ := eq20471
       grind)
    | exact superpose eq20471 eq21407
    | exact resolve eq21407 eq20471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20471 eq21407
  have eq21418 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21414 eq21
    | exact resolve eq21 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21606 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21418
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21418
    | exact resolve eq21418 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21418
  have eq22118 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq21414 eq21402
    | exact resolve eq21402 eq21414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21402 eq21414
  have eq22119 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22118 eq15
    | exact resolve eq15 eq22118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22118
  have eq22220 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22119
    | exact resolve eq22119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22119
  have eq22255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21606 eq22220
    | exact resolve eq22220 eq21606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21606 eq22220
  have eq22286 : False := by grind
  exact eq22286

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pxx_pyx_pxy_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X1 (M.op X1 (M.op (M.op X2 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X1 (M.op (M.op X2 X0) X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X1 (M.op X1 (M.op (M.op X2 X0) X0))
       grind)
    | (have r₁ := eq12 X1 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 X1)))
       have r₂ := eq9 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq87 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq42
    | exact resolve eq42 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq42
    | exact resolve eq42 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq34 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq242 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq259 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op (M.op X2 X1) X1))) = (M.op (M.op (M.op X2 X1) X1) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X2 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq242 (M.op (M.op X2 X1) X1) X1 X3
       have i₂ := eq242 X1 X2 X0
       grind)
    | exact superpose eq242 eq242
    | exact resolve eq242 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq242 X1 x X3
       have i₂ := eq242 X1 x X0
       grind)
    | exact superpose eq242 eq242
    | exact resolve eq242 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq242 X1 x X0
       grind)
    | exact superpose eq242 eq9
    | exact resolve eq9 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 (M.op X2 X0) X2
       have i₂ := eq242 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq242 eq21
    | exact resolve eq21 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq283 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq283
    | exact resolve eq283 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq301 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X1) X1) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X2 X1) X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259 X0 X1 X2 x
       have i₂ := eq9 X1 x X2
       grind)
    | exact superpose eq9 eq259
    | exact resolve eq259 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq316 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq273 X0 (M.op X0 X0)
       have i₂ := eq273 X0 X0
       grind)
    | exact superpose eq273 eq273
    | exact resolve eq273 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq21
    | exact resolve eq21 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq326 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq323 X1 X0 X2
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq323
    | exact resolve eq323 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq332 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq65
    | (have j0 := eq65 (k (τ X0) X1) X2
       grind)
    | exact resolve eq65 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (k X1 (τ X0)) X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq65
    | (have j0 := eq65 (k X0 (τ X1)) X2
       grind)
    | exact resolve eq65 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq359 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq333 X0 X1 X2
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq333
    | (have j0 := eq333 X0 X1 X2
       grind)
    | exact resolve eq333 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq360 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq332 X0 X1 X2
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq332
    | (have j0 := eq332 X0 X1 X2
       grind)
    | exact resolve eq332 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq364 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq359 X0 X1 X2
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq359
    | (have j0 := eq359 X0 X1 X2
       grind)
    | exact resolve eq359 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq359
  have eq365 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq360 X0 X1 X2
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq360
    | (have j0 := eq360 X0 X1 X2
       grind)
    | exact resolve eq360 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq360
  have eq378 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq9
    | exact resolve eq9 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq273 (M.op X0 X0) X0
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq273
    | exact resolve eq273 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X1 (M.op X1 (M.op X0 X0))
       have i₂ := eq378 X0 X1
       grind)
    | exact superpose eq378 eq273
    | exact resolve eq273 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq473 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq264 X1 (M.op X2 (M.op X0 X0)) X2
       have i₂ := eq378 X0 X2
       grind)
    | exact superpose eq378 eq264
    | exact resolve eq264 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq264 X1 (σ X0) (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq264
    | exact resolve eq264 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X1
       have i₂ := eq291 X1 X0 X1
       grind)
    | (have i₁ := eq316 X1
       have i₂ := eq291 X1 X1 X0
       grind)
    | exact superpose eq291 eq316
    | exact resolve eq316 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq316
  have eq799 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq326 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq378 X0 X1
       grind)
    | exact superpose eq378 eq326
    | exact resolve eq326 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 X1 x
       have i₂ := eq473 X0 x X1
       grind)
    | exact superpose eq473 eq799
    | exact resolve eq799 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq799
  have eq1009 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq384 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq384
    | exact resolve eq384 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq1031 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1009 X0
       have i₂ := eq42 (M.op X0 X0)
       grind)
    | exact superpose eq42 eq1009
    | exact resolve eq1009 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1035 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1031 X0
       have i₂ := eq886 X0 (M.op X0 X0)
       grind)
    | exact superpose eq886 eq1031
    | exact resolve eq1031 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1039 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1035 X0
       have i₂ := eq614 X0 X0
       grind)
    | exact superpose eq614 eq1035
    | exact resolve eq1035 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1596 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X1 (M.op X0 X1)
       have i₂ := eq886 X1 X0
       grind)
    | (have i₁ := eq614 X1 (M.op X0 X0)
       have i₂ := eq886 X0 X1
       grind)
    | exact superpose eq886 eq614
    | exact resolve eq614 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1598 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq326 X1 X0 X0
       have i₂ := eq886 (M.op X0 X1) X0
       grind)
    | exact superpose eq886 eq326
    | exact resolve eq326 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq1601 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq414 X1 X0
       grind)
    | exact superpose eq414 eq1596
    | exact resolve eq1596 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq1596
  have eq1744 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) = (M.op (M.op (M.op X3 X1) X1) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq139 (M.op (M.op X1 X0) X0) X1 X0
       have i₂ := eq242 X0 X1 X2
       grind)
    | exact superpose eq242 eq139
    | exact resolve eq139 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq242
  have eq1838 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1744 X0 X1 X2 X3
       have i₂ := eq301 X0 X1 X3
       grind)
    | exact superpose eq301 eq1744
    | exact resolve eq1744 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq1744
  have eq1875 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1)) (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1838 X0 X1 x X3
       have i₂ := eq614 x (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1))
       grind)
    | exact superpose eq614 eq1838
    | exact resolve eq1838 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1897 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op (M.op X3 X1) X1) (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1875 X0 X1 X3
       have i₂ := eq1601 (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) X1)
       grind)
    | exact superpose eq1601 eq1875
    | exact resolve eq1875 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1913 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X3 X1) (M.op X1 X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1897 X0 X1 X3
       have i₂ := eq1601 (M.op X3 X1) X1
       grind)
    | exact superpose eq1601 eq1897
    | exact resolve eq1897 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq1897
  have eq1924 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op (M.op X3 X1) X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1913 X0 X1 X3
       have i₂ := eq886 X1 (M.op X3 X1)
       grind)
    | exact superpose eq886 eq1913
    | exact resolve eq1913 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq1913
  have eq1934 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1924 X0 X1 x
       have i₂ := eq614 x X1
       grind)
    | exact superpose eq614 eq1924
    | exact resolve eq1924 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924
  have eq2962 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X1
       have i₂ := eq264 X1 X1 X0
       grind)
    | (have i₁ := eq1039 X1
       have i₂ := eq264 X0 X1 X1
       grind)
    | exact superpose eq264 eq1039
    | exact resolve eq1039 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq3737 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1598 (σ X1) (σ (M.op X0 (M.op X0 X1)))
       have i₂ := eq2962 X0 X1
       grind)
    | exact superpose eq2962 eq1598
    | exact resolve eq1598 eq2962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962
  have eq3740 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3737 X0 X1
       have i₂ := eq484 X0 (σ X0)
       grind)
    | exact superpose eq484 eq3737
    | exact resolve eq3737 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484 eq3737
  have eq5401 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) ≠ X0 ∨ (k (M.op X0 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 (M.op X1 X1)) X1
       have i₂ := eq1934 X1 X1
       grind)
    | exact superpose eq1934 eq12
    | exact resolve eq12 eq1934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5402 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (M.op (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    grind
  clear eq1934
  have eq5480 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5402 X0
       have i₂ := eq378 X0 X0
       grind)
    | exact superpose eq378 eq5402
    | (have j0 := eq5402 X0
       grind)
    | exact resolve eq5402 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq5402
  have eq5548 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5480 X0
       have j1 := eq5401 X0 X0
       grind)
    | (have r₁ := eq5480 x
       have r₂ := eq5401 x x
       grind)
    | exact resolve eq5480 eq5401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401 eq5480
  have eq5706 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5548 X1
       have i₂ := eq264 X1 X1 X0
       grind)
    | (have i₁ := eq5548 X1
       have i₂ := eq264 X0 X1 X1
       grind)
    | exact superpose eq264 eq5548
    | exact resolve eq5548 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq5548
  have eq6116 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (M.op X1 (M.op X1 (σ X0))) X0
       have i₂ := eq5706 X1 (σ X0)
       grind)
    | exact superpose eq5706 eq25
    | exact resolve eq25 eq5706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6117 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X1 (τ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 (M.op X1 (τ X0)))
       have i₂ := eq5706 X1 (τ X0)
       grind)
    | exact superpose eq5706 eq19
    | exact resolve eq19 eq5706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5706
  have eq6118 : ∀ X0 X1 : G, (k (σ (M.op X1 (M.op X1 (τ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6117 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6117
    | exact resolve eq6117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117
  have eq6119 : ∀ X0 X1 : G, (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6116 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6116
    | exact resolve eq6116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6116
  have eq6739 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 (M.op X1 (τ (τ X0)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (σ (M.op X1 (M.op X1 (τ (τ X0)))))
       have i₂ := eq6118 (τ X0) X1
       grind)
    | exact superpose eq6118 eq19
    | exact resolve eq19 eq6118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6118
  have eq6740 : ∀ X0 X1 : G, (k (σ (σ (M.op X1 (M.op X1 (τ (τ X0)))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6739 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6739
    | exact resolve eq6739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6739
  have eq6871 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 (M.op X1 (σ (σ X0)))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (τ (M.op X1 (M.op X1 (σ (σ X0))))) X0
       have i₂ := eq6119 (σ X0) X1
       grind)
    | exact superpose eq6119 eq25
    | exact resolve eq25 eq6119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq6874 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 (M.op X1 (σ (σ X0)))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6871 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6871
    | exact resolve eq6871 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871
  have eq17214 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) (M.op (k (σ X0) X1) (M.op (M.op X3 (M.op (k (σ X0) X1) (σ X2))) (M.op (k (σ X0) X1) (σ X2))))) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 (k (σ X0) X1) X1
       have i₂ := eq364 X0 X1 X2
       grind)
    | exact superpose eq364 eq181
    | (have j1 := eq364 X0 X1 X2
       grind)
    | exact resolve eq181 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq17398 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) (M.op (k (σ X0) X1) (M.op (M.op (k (σ X0) X1) (σ X2)) (M.op (k (σ X0) X1) (σ X2))))) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17214 X0 X1 X2 x
       have i₂ := eq614 x (M.op (k (σ X0) X1) (σ X2))
       grind)
    | exact superpose eq614 eq17214
    | (have j0 := eq17214 X0 X1 X2 x
       grind)
    | exact resolve eq17214 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17214
  have eq17452 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17398 X0 X1 X2
       have i₂ := eq1598 (k (σ X0) X1) (σ X2)
       grind)
    | exact superpose eq1598 eq17398
    | (have j0 := eq17398 X0 X1 X2
       grind)
    | exact resolve eq17398 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17398
  have eq17485 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17452 X0 X1 X2
       have i₂ := eq30 X0 X1 X2
       grind)
    | exact superpose eq30 eq17452
    | (have j0 := eq17452 X0 X1 X2
       grind)
    | exact resolve eq17452 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17452
  have eq17486 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ X2) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq17485 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17485
  have eq18856 : ∀ X0 X1 X2 X3 : G, (M.op (k X0 (σ X1)) (σ X2)) = (k (k X0 (σ X1)) (M.op (k X0 (σ X1)) (M.op (M.op X3 (M.op (k X0 (σ X1)) (σ X2))) (M.op (k X0 (σ X1)) (σ X2))))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 (k X0 (σ X1)) X1
       have i₂ := eq365 X0 X1 X2
       grind)
    | exact superpose eq365 eq181
    | (have j1 := eq365 X0 X1 X2
       grind)
    | exact resolve eq181 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq365
  have eq19044 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (σ X2)) = (k (k X0 (σ X1)) (M.op (k X0 (σ X1)) (M.op (M.op (k X0 (σ X1)) (σ X2)) (M.op (k X0 (σ X1)) (σ X2))))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18856 X0 X1 X2 x
       have i₂ := eq614 x (M.op (k X0 (σ X1)) (σ X2))
       grind)
    | exact superpose eq614 eq18856
    | (have j0 := eq18856 X0 X1 X2 x
       grind)
    | exact resolve eq18856 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq18856
  have eq19098 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19044 X0 X1 X2
       have i₂ := eq1598 (k X0 (σ X1)) (σ X2)
       grind)
    | exact superpose eq1598 eq19044
    | (have j0 := eq19044 X0 X1 X2
       grind)
    | exact resolve eq19044 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598 eq19044
  have eq19132 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19098 X0 X1 X2
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq19098
    | (have j0 := eq19098 X0 X1 X2
       grind)
    | exact resolve eq19098 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19098
  have eq19133 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq19132 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19132
  have eq32172 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))
       have i₂ := eq6740 (τ X0) X1
       grind)
    | exact superpose eq6740 eq19
    | exact resolve eq19 eq6740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32179 : ∀ X0 X1 : G, (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32172 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32172
    | exact resolve eq32172 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32172
  have eq189565 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0) (σ X2)) ∨ (σ X2) = (M.op (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0) (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17486 (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0))))))) X0 X2
       have i₂ := eq6740 (τ X0) X1
       grind)
    | exact superpose eq6740 eq17486
    | (have j0 := eq17486 (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0))))))) X0 X2
       grind)
    | exact resolve eq17486 eq6740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6740 eq17486
  have eq189733 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = (M.op (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0) (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189565 X0 X1 X2
       have i₂ := eq32179 X0 X1
       grind)
    | exact superpose eq32179 eq189565
    | (have j0 := eq189565 X0 X1 X2
       grind)
    | exact resolve eq189565 eq32179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189565
  have eq189787 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = (M.op (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0) (k (σ (σ (σ (M.op X1 (M.op X1 (τ (τ (τ X0)))))))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189733 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq189733
    | (have j0 := eq189733 X0 X1 X2
       grind)
    | exact resolve eq189733 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq189733
  have eq189824 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (M.op X0 X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq189787 X0 x X2
       have i₂ := eq32179 X0 x
       grind)
    | exact superpose eq32179 eq189787
    | (have j0 := eq189787 X0 x X2
       grind)
    | exact resolve eq189787 eq32179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32179 eq189787
  have eq192909 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (k (τ (M.op X1 (M.op X1 (σ (σ X0))))) (σ X0)) (σ X2)) ∨ (σ X2) = (M.op (k (τ (M.op X1 (M.op X1 (σ (σ X0))))) (σ X0)) (k (τ (M.op X1 (M.op X1 (σ (σ X0))))) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19133 (τ (M.op X1 (M.op X1 (σ (σ X0))))) X0 X2
       have i₂ := eq6874 X0 X1
       grind)
    | exact superpose eq6874 eq19133
    | (have j0 := eq19133 (τ (M.op X1 (M.op X1 (σ (σ X0))))) X0 X2
       grind)
    | exact resolve eq19133 eq6874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6874 eq19133
  have eq193101 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X2) = (M.op (k (τ (M.op X1 (M.op X1 (σ (σ X0))))) (σ X0)) (k (τ (M.op X1 (M.op X1 (σ (σ X0))))) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192909 X0 X1 X2
       have i₂ := eq6119 (σ X0) X1
       grind)
    | exact superpose eq6119 eq192909
    | (have j0 := eq192909 X0 X1 X2
       grind)
    | exact resolve eq192909 eq6119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192909
  have eq193158 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq193101 X0 x X2
       have i₂ := eq6119 (σ X0) x
       grind)
    | exact superpose eq6119 eq193101
    | (have j0 := eq193101 X0 x X2
       grind)
    | exact resolve eq193101 eq6119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6119 eq193101
  have eq193197 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X2) = (σ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq193158 X0 X2
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq193158
    | (have j0 := eq193158 X0 X2
       grind)
    | exact resolve eq193158 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq193158
  have eq280439 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq189824 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189824
    | exact resolve eq189824 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189824
  have eq280733 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq280439 (τ X1) X0
       grind)
    | exact superpose eq280439 eq19
    | (have j1 := eq280439 (τ X1) X0
       grind)
    | exact resolve eq19 eq280439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq280439
  have eq765432 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq280733 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq280733
    | exact resolve eq280733 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280733
  have eq766047 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq765432 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq765432
    | (have j0 := eq765432 X0 X1
       grind)
    | exact resolve eq765432 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765432
  have eq1729192 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq193197 x y
       grind)
    | exact superpose eq193197 eq16
    | (have j1 := eq193197 x y
       grind)
    | exact resolve eq16 eq193197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193197
  have eq1734805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1729192
       have i₂ := eq766047 y x
       grind)
    | exact superpose eq766047 eq1729192
    | (have j1 := eq766047 y x
       grind)
    | (have r₁ := eq1729192
       have r₂ := eq766047 y x
       grind)
    | exact resolve eq1729192 eq766047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766047 eq1729192
  have eq1734813 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq1734805
  have eq1734884 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1734813
       grind)
    | exact superpose eq1734813 eq10
    | exact resolve eq10 eq1734813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734813
  have eq1735309 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1734884
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1734884
    | exact resolve eq1734884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734884
  have eq1735310 : y = (M.op x x) := by grind
  clear eq1735309
  have eq1738297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3740 x x
       have i₂ := eq1735310
       grind)
    | exact superpose eq1735310 eq3740
    | exact resolve eq3740 eq1735310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740 eq1735310
  have eq1738604 : False := by grind
  exact eq1738604
