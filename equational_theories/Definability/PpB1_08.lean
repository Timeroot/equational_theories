import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_pyx_Equation1484 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 X0
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq280 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq278 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq278 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq278 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq291 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq280 (σ X0)
       grind)
    | exact superpose eq280 eq15
    | exact resolve eq15 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq291
    | exact resolve eq291 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq355 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq9
    | exact resolve eq9 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq9
    | exact resolve eq9 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq310 X0
       grind)
    | exact superpose eq310 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq358 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq358 X0 X1
       grind)
    | exact resolve eq357 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq469 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq359 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq359
    | exact resolve eq359 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq359 X0 (σ X1)
       grind)
    | exact superpose eq359 eq15
    | (have j1 := eq359 X0 (σ X1)
       grind)
    | exact resolve eq15 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq509 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq469 (τ X0) X1
       grind)
    | exact superpose eq469 eq18
    | (have j1 := eq469 (τ X0) X1
       grind)
    | exact resolve eq18 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq469
  have eq793 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq509 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq509
    | exact resolve eq509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq850 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq793
    | (have j0 := eq793 X0 X1
       grind)
    | exact resolve eq793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq1235 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq480 x y
       grind)
    | exact superpose eq480 eq16
    | (have j1 := eq480 x y
       grind)
    | exact resolve eq16 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq480 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq1424 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1235
       have i₂ := eq850 x y
       grind)
    | exact superpose eq850 eq1235
    | (have j1 := eq850 (σ x) (σ y)
       grind)
    | (have r₁ := eq1235
       have r₂ := eq850 x y
       grind)
    | exact resolve eq1235 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1425 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1424
  have eq1428 : y ≠ y ∨ x = (M.op x x) ∨ (k y x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1425
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1425
       grind)
    | exact resolve eq13 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : ∀ X0 : G, y = (M.op (M.op X0 y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq63 y x x
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq63
    | exact resolve eq63 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : (k y x) = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1428
  have eq1436 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1429 x
       have i₂ := eq1425
       grind)
    | exact superpose eq1425 eq1429
    | exact resolve eq1429 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425 eq1429
  have eq1442 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1436
  have eq1446 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq356 y (σ x)
       have i₂ := eq1442
       grind)
    | exact superpose eq1442 eq356
    | exact resolve eq356 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq1449 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq63 (σ y) x (σ x)
       have i₂ := eq1442
       grind)
    | exact superpose eq1442 eq63
    | exact resolve eq63 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1455 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1446
       have i₂ := eq310 y
       grind)
    | exact superpose eq310 eq1446
    | exact resolve eq1446 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1458 : y = (M.op y y) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq1455
       have i₂ := eq310 (M.op y y)
       grind)
    | exact superpose eq310 eq1455
    | exact resolve eq1455 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455
  have eq1466 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1449 (σ x)
       have i₂ := eq1442
       grind)
    | exact superpose eq1442 eq1449
    | exact resolve eq1449 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq1449
  have eq1477 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1466
  have eq1482 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1477
       have i₂ := eq310 y
       grind)
    | exact superpose eq310 eq1477
    | exact resolve eq1477 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1490 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq358 y X0
       have i₂ := eq1482
       grind)
    | exact superpose eq1482 eq358
    | (have j0 := eq358 y X0
       grind)
    | (have r₁ := eq358 y x
       have r₂ := eq1482
       grind)
    | exact resolve eq358 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1505 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq1490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1510 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1505 X0
       have j1 := eq358 y X0
       grind)
    | (have r₁ := eq1505 X0
       have r₂ := eq358 y x
       grind)
    | exact resolve eq1505 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1524 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq1510 (σ X0)
       grind)
    | exact superpose eq1510 eq15
    | exact resolve eq15 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1614 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 y)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq355 X0 (σ y)
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq355
    | exact resolve eq355 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq1524
  have eq2804 : (σ y) = (M.op (σ (k y y)) (M.op (σ y) (σ y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq1614 y
       have i₂ := eq1458
       grind)
    | exact superpose eq1458 eq1614
    | exact resolve eq1614 eq1458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458 eq1614
  have eq2814 : (σ y) = (M.op (σ (k y y)) (σ (M.op y y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq2804
       have i₂ := eq310 y
       grind)
    | exact superpose eq310 eq2804
    | exact resolve eq2804 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq2822 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq2814
       have i₂ := eq280 y
       grind)
    | exact superpose eq280 eq2814
    | exact resolve eq2814 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq2814
  have eq2826 : (σ y) = (σ (M.op (M.op y y) (M.op y y))) ∨ (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq2822
       have i₂ := eq310 (M.op y y)
       grind)
    | exact superpose eq310 eq2822
    | exact resolve eq2822 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq2827 : (σ y) = (σ (M.op (M.op y y) (M.op y y))) := by grind
  clear eq2826
  have eq2830 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2827
       have i₂ := eq1482
       grind)
    | exact superpose eq1482 eq2827
    | exact resolve eq2827 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482 eq2827
  have eq2884 : (σ y) = (σ (M.op y y)) := by grind
  clear eq2830
  have eq128946 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1266 x y
       have i₂ := eq1432
       grind)
    | exact superpose eq1432 eq1266
    | (have j0 := eq1266 x y
       grind)
    | exact resolve eq1266 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq128967 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq128946
  have eq128980 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq128967
       have r₂ := eq2884
       grind)
    | exact resolve eq128967 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128967
  have eq128985 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128980
       grind)
    | exact superpose eq128980 eq16
    | exact resolve eq16 eq128980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129030 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq128980
       grind)
    | exact superpose eq128980 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq128980
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq128980
       grind)
    | exact resolve eq13 eq128980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128980
  have eq129038 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq129030
  have eq129043 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129038
       have i₂ := eq310 x
       grind)
    | exact superpose eq310 eq129038
    | exact resolve eq129038 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129038
  have eq129083 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129043
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq129043
    | exact resolve eq129043 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129043
  have eq129118 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129083
       have i₂ := eq310 y
       grind)
    | exact superpose eq310 eq129083
    | exact resolve eq129083 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310 eq129083
  have eq129133 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq129118
       have i₂ := eq2884
       grind)
    | exact superpose eq2884 eq129118
    | exact resolve eq129118 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884 eq129118
  have eq129153 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq358 x X0
       have i₂ := eq129133
       grind)
    | exact superpose eq129133 eq358
    | (have j0 := eq358 x X0
       grind)
    | (have r₁ := eq358 x x
       have r₂ := eq129133
       grind)
    | exact resolve eq358 eq129133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129133
  have eq129225 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have j0 := eq129153 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129153
  have eq129251 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have j0 := eq129225 X0
       have j1 := eq358 x X0
       grind)
    | (have r₁ := eq129225 X0
       have r₂ := eq358 x x
       grind)
    | exact resolve eq129225 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq129225
  have eq129319 : ∀ X0 : G, (σ y) = (σ (k y x)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq129251 (σ X0)
       grind)
    | exact superpose eq129251 eq15
    | exact resolve eq15 eq129251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129251
  have eq130179 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1266 x y
       have i₂ := eq129319 X0
       grind)
    | exact superpose eq129319 eq1266
    | (have j0 := eq1266 x y
       have j1 := eq129319 X0
       grind)
    | (have r₁ := eq1266 x y
       have r₂ := eq129319 X0
       grind)
    | exact resolve eq1266 eq129319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq130377 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq130179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130179
  have eq132901 : (σ y) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq130377 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130377
  have eq132904 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j1 := eq129319 y
       grind)
    | (have r₁ := eq132901
       have r₂ := eq129319 x
       grind)
    | exact resolve eq132901 eq129319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129319 eq132901
  have eq133018 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq132904
       grind)
    | exact superpose eq132904 eq16
    | exact resolve eq16 eq132904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132904
  have eq133208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq133018
       have i₂ := eq850 x y
       grind)
    | exact superpose eq850 eq133018
    | (have j1 := eq850 x y
       grind)
    | (have r₁ := eq133018
       have r₂ := eq850 x y
       grind)
    | exact resolve eq133018 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq133209 : y = (M.op x y) := by grind
  clear eq133208
  have eq133228 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq128985
       have i₂ := eq133209
       grind)
    | exact superpose eq133209 eq128985
    | exact resolve eq128985 eq133209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128985 eq133209
  have eq133280 : x = (M.op x x) := by grind
  clear eq133228
  have eq133316 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq133280
       grind)
    | exact superpose eq133280 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq133280
       grind)
    | exact resolve eq12 eq133280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133280
  have eq133393 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq133316 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133316
  have eq133598 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq133018
       have i₂ := eq133393 y
       grind)
    | exact superpose eq133393 eq133018
    | exact resolve eq133018 eq133393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133018 eq133393
  have eq133609 : False := by grind
  exact eq133609

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1484 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq64 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq102 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq99 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq99
    | (have j0 := eq99 X0 X1
       grind)
    | exact resolve eq99 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq261 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102 x y
       grind)
    | exact superpose eq102 eq16
    | (have j1 := eq102 x y
       grind)
    | exact resolve eq16 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq1195 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq261
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq261
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq261
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq261
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq261 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq1196 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1195
  have eq1306 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 (τ X1) (τ X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq268
    | (have j0 := eq268 (τ X1) (τ X0)
       grind)
    | exact resolve eq268 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1315 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1306 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1306
    | (have j0 := eq1306 X0 X1
       grind)
    | exact resolve eq1306 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1326 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1315 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1315
    | (have j0 := eq1315 X0 X1
       grind)
    | exact resolve eq1315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1334 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1326 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1326
    | (have j0 := eq1326 X0 X1
       grind)
    | exact resolve eq1326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1338 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1334 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1334
    | (have j0 := eq1334 X0 X1
       grind)
    | exact resolve eq1334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1340 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1338 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1338
    | (have j0 := eq1338 X0 X1
       grind)
    | exact resolve eq1338 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1338
  have eq1342 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1340 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1340
    | (have j0 := eq1340 X0 X1
       grind)
    | exact resolve eq1340 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340
  have eq1343 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1342 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1342
    | (have j0 := eq1342 X0 X1
       grind)
    | exact resolve eq1342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq10279 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1196
       grind)
    | exact superpose eq1196 eq16
    | exact resolve eq16 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq10280 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq10279
       have r₂ := eq22 x
       grind)
    | exact resolve eq10279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10279
  have eq10283 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10280
       grind)
    | exact superpose eq10280 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10280
       grind)
    | exact resolve eq13 eq10280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10280
  have eq10290 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq10283
  have eq23517 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10290
       grind)
    | exact superpose eq10290 eq16
    | exact resolve eq16 eq10290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10290
  have eq23518 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq23517
       have r₂ := eq22 x
       grind)
    | exact resolve eq23517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23517
  have eq23521 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq64 x (σ y)
       have i₂ := eq23518
       grind)
    | exact superpose eq23518 eq64
    | (have j0 := eq64 x (σ y)
       grind)
    | (have r₁ := eq64 x (σ y)
       have r₂ := eq23518
       grind)
    | exact resolve eq64 eq23518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23518
  have eq23547 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by grind
  clear eq23521
  have eq23548 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by grind
  clear eq23547
  have eq23555 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq23548
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq23548
    | exact resolve eq23548 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23548
  have eq23916 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq268 x y
       have i₂ := eq23555
       grind)
    | exact superpose eq23555 eq268
    | (have j0 := eq268 x y
       grind)
    | (have r₁ := eq268 x y
       have r₂ := eq23555
       grind)
    | exact resolve eq268 eq23555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23555
  have eq23943 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq23916
  have eq23944 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq23943
  have eq23953 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq268 x y
       grind)
    | (have r₁ := eq23944
       have r₂ := eq268 x y
       grind)
    | exact resolve eq23944 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq23944
  have eq24108 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23953
       grind)
    | exact superpose eq23953 eq16
    | exact resolve eq16 eq23953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24109 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64 x (σ y)
       have i₂ := eq23953
       grind)
    | exact superpose eq23953 eq64
    | (have j0 := eq64 x (σ y)
       grind)
    | (have r₁ := eq64 x (σ y)
       have r₂ := eq23953
       grind)
    | exact resolve eq64 eq23953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq23953
  have eq24135 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq24109
  have eq24136 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq24135
  have eq24143 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24136
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq24136
    | exact resolve eq24136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24136
  have eq24591 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24143
       grind)
    | exact superpose eq24143 eq10
    | exact resolve eq10 eq24143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24143
  have eq24787 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24591
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24591
    | exact resolve eq24591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24591
  have eq24789 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24787
       grind)
    | exact superpose eq24787 eq16
    | exact resolve eq16 eq24787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24787
  have eq24790 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq24789
       have r₂ := eq22 x
       grind)
    | exact resolve eq24789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24789
  have eq25241 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq24790
       grind)
    | exact superpose eq24790 eq10
    | exact resolve eq10 eq24790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24790
  have eq25439 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq25241
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq25241
    | exact resolve eq25241 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25241
  have eq25455 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1343 y x
       have i₂ := eq25439
       grind)
    | exact superpose eq25439 eq1343
    | (have j0 := eq1343 y x
       grind)
    | (have r₁ := eq1343 y x
       have r₂ := eq25439
       grind)
    | exact resolve eq1343 eq25439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq25439
  have eq25477 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq25455
  have eq25950 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25477
       grind)
    | exact superpose eq25477 eq16
    | exact resolve eq16 eq25477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25477
  have eq25953 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq25950
       have r₂ := eq22 x
       grind)
    | exact resolve eq25950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25950
  have eq25954 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq24108
       have i₂ := eq25953
       grind)
    | exact superpose eq25953 eq24108
    | exact resolve eq24108 eq25953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24108
  have eq25970 : (σ x) = (σ y) := by grind
  clear eq25954
  have eq26348 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25970
       grind)
    | exact superpose eq25970 eq16
    | exact resolve eq16 eq25970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25970
  have eq26547 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26348
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq26348
    | exact resolve eq26348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26348
  have eq26548 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq26547
       have i₂ := eq25953
       grind)
    | exact superpose eq25953 eq26547
    | exact resolve eq26547 eq25953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25953 eq26547
  have eq26549 : False := by grind
  exact eq26549

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1484 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq18
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq251 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have j1 := eq97 x y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq813 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 (τ X1) (τ X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq258
    | (have j0 := eq258 (τ X1) (τ X0)
       grind)
    | exact resolve eq258 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq820 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq813 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq813
    | (have j0 := eq813 X0 X1
       grind)
    | exact resolve eq813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq823 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq825 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq823 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq823
    | (have j0 := eq823 X0 X1
       grind)
    | exact resolve eq823 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq826 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq825
    | (have j0 := eq825 X0 X1
       grind)
    | exact resolve eq825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq827 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq828 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq1054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq251
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq251
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq251
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq251
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq251 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq1055 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1054
  have eq5280 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1055
       grind)
    | exact superpose eq1055 eq16
    | exact resolve eq16 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq5281 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5280
       have r₂ := eq22 x
       grind)
    | exact resolve eq5280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5280
  have eq5284 : y ≠ y ∨ y = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq5281
       grind)
    | exact superpose eq5281 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5281
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5281
       grind)
    | exact resolve eq13 eq5281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5281
  have eq5293 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5284
  have eq10604 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5293
       grind)
    | exact superpose eq5293 eq16
    | exact resolve eq16 eq5293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5293
  have eq10605 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq10604
       have r₂ := eq22 x
       grind)
    | exact resolve eq10604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10604
  have eq10727 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq258 x y
       have i₂ := eq10605
       grind)
    | exact superpose eq10605 eq258
    | (have j0 := eq258 x y
       grind)
    | exact resolve eq258 eq10605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq10605
  have eq10749 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10727
  have eq10750 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq10749
  have eq10761 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10750
       grind)
    | exact superpose eq10750 eq16
    | exact resolve eq16 eq10750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10769 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq10750
       grind)
    | exact superpose eq10750 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10750
       grind)
    | exact resolve eq13 eq10750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10750
  have eq10780 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq10769
  have eq10781 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq10780
  have eq10789 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10781
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq10781
    | exact resolve eq10781 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10781
  have eq10967 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10789
       grind)
    | exact superpose eq10789 eq10
    | exact resolve eq10 eq10789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10789
  have eq11065 : x = y ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10967
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10967
    | exact resolve eq10967 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10967
  have eq11230 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11065
       grind)
    | exact superpose eq11065 eq16
    | exact resolve eq16 eq11065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11065
  have eq11231 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq11230
       have r₂ := eq22 x
       grind)
    | exact resolve eq11230 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11230
  have eq11245 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq11231
       grind)
    | exact superpose eq11231 eq10
    | exact resolve eq10 eq11231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11231
  have eq11344 : y = (k y x) := by
    first
    | (have i₁ := eq11245
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq11245
    | exact resolve eq11245 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11245
  have eq11426 : y ≠ y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq828 y x
       have i₂ := eq11344
       grind)
    | exact superpose eq11344 eq828
    | (have j0 := eq828 y x
       grind)
    | (have r₁ := eq828 y x
       have r₂ := eq11344
       grind)
    | exact resolve eq828 eq11344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq11344
  have eq11443 : y = (M.op x y) ∨ x = y := by grind
  clear eq11426
  have eq11447 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10761
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq10761
    | exact resolve eq10761 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10761 eq11443
  have eq11468 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq11447
  have eq11663 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11468
       grind)
    | exact superpose eq11468 eq16
    | exact resolve eq16 eq11468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq11668 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq11663
       have r₂ := eq22 x
       grind)
    | exact resolve eq11663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11663
  have eq11669 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11668
       grind)
    | exact superpose eq11668 eq16
    | exact resolve eq16 eq11668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11670 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11668
       grind)
    | exact superpose eq11668 eq10
    | exact resolve eq10 eq11668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11668
  have eq11771 : x = y := by
    first
    | (have i₁ := eq11670
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11670
    | exact resolve eq11670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11670
  have eq11772 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11669
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11669
    | exact resolve eq11669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq11669
  have eq11773 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11772
       have i₂ := eq11771
       grind)
    | exact superpose eq11771 eq11772
    | exact resolve eq11772 eq11771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11771 eq11772
  have eq11774 : False := by grind
  exact eq11774

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1484 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  clear eq18
  have eq51 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq97 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq251 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq16
    | (have j1 := eq97 x y
       grind)
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq795 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 (τ X1) (τ X0)
       have i₂ := eq51 X1 X0
       grind)
    | exact superpose eq51 eq258
    | (have j0 := eq258 (τ X1) (τ X0)
       grind)
    | exact resolve eq258 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq802 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq795
    | (have j0 := eq795 X0 X1
       grind)
    | exact resolve eq795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq805 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq802 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq802
    | (have j0 := eq802 X0 X1
       grind)
    | exact resolve eq802 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq807 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq805
    | (have j0 := eq805 X0 X1
       grind)
    | exact resolve eq805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq808 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq807 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq807
    | (have j0 := eq807 X0 X1
       grind)
    | exact resolve eq807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq809 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq808
    | (have j0 := eq808 X0 X1
       grind)
    | exact resolve eq808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq810 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq809
    | (have j0 := eq809 X0 X1
       grind)
    | exact resolve eq809 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq251
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq251
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq251
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq251
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq251 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq963 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq962
  have eq5107 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq963
       grind)
    | exact superpose eq963 eq16
    | exact resolve eq16 eq963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq5108 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5107
       have r₂ := eq22 x
       grind)
    | exact resolve eq5107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5111 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq5108
       grind)
    | exact superpose eq5108 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5108
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5108
       grind)
    | exact resolve eq13 eq5108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5108
  have eq5119 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5111
  have eq9346 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5119
       grind)
    | exact superpose eq5119 eq16
    | exact resolve eq16 eq5119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119
  have eq9347 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq9346
       have r₂ := eq22 x
       grind)
    | exact resolve eq9346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9346
  have eq9530 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9347
       grind)
    | exact superpose eq9347 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9347
       grind)
    | exact resolve eq13 eq9347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9347
  have eq9540 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq9530
  have eq9541 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq9540
  have eq9543 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9541
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9541
    | exact resolve eq9541 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9541
  have eq9723 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq258 x y
       have i₂ := eq9543
       grind)
    | exact superpose eq9543 eq258
    | (have j0 := eq258 x y
       grind)
    | (have r₁ := eq258 x y
       have r₂ := eq9543
       grind)
    | exact resolve eq258 eq9543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9543
  have eq9745 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq9723
  have eq9746 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq9745
  have eq9754 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq258 x y
       grind)
    | (have r₁ := eq9746
       have r₂ := eq258 x y
       grind)
    | exact resolve eq9746 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq9746
  have eq9761 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9754
       grind)
    | exact superpose eq9754 eq16
    | exact resolve eq16 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9768 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9754
       grind)
    | exact superpose eq9754 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9754
       grind)
    | exact resolve eq13 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754
  have eq9778 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9768
  have eq9779 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9778
  have eq9781 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9779
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9779
    | exact resolve eq9779 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9779
  have eq9980 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9781
       grind)
    | exact superpose eq9781 eq10
    | exact resolve eq10 eq9781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9781
  have eq10075 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq9980
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9980
    | exact resolve eq9980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9980
  have eq10275 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10075
       grind)
    | exact superpose eq10075 eq16
    | exact resolve eq16 eq10075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10075
  have eq10276 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq10275
       have r₂ := eq22 x
       grind)
    | exact resolve eq10275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10275
  have eq10290 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq10276
       grind)
    | exact superpose eq10276 eq10
    | exact resolve eq10 eq10276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10276
  have eq10388 : x = (k y x) := by
    first
    | (have i₁ := eq10290
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10290
    | exact resolve eq10290 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10290
  have eq10497 : x ≠ x ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq810 y x
       have i₂ := eq10388
       grind)
    | exact superpose eq10388 eq810
    | (have j0 := eq810 y x
       grind)
    | (have r₁ := eq810 y x
       have r₂ := eq10388
       grind)
    | exact resolve eq810 eq10388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq10388
  have eq10514 : x = y ∨ x = (M.op x y) := by grind
  clear eq10497
  have eq10518 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10514
       grind)
    | exact superpose eq10514 eq16
    | exact resolve eq16 eq10514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10514
  have eq10523 : x = (M.op x y) := by
    first
    | (have r₁ := eq10518
       have r₂ := eq22 x
       grind)
    | exact resolve eq10518 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10518
  have eq10623 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9761
       have i₂ := eq10523
       grind)
    | exact superpose eq10523 eq9761
    | exact resolve eq9761 eq10523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9761 eq10523
  have eq10639 : (σ x) = (σ y) := by grind
  clear eq10623
  have eq10641 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10639
       grind)
    | exact superpose eq10639 eq10
    | exact resolve eq10 eq10639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10639
  have eq10738 : x = y := by
    first
    | (have i₁ := eq10641
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10641
    | exact resolve eq10641 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10641
  have eq10836 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10738
       grind)
    | exact superpose eq10738 eq16
    | exact resolve eq16 eq10738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10738
  have eq10842 : False := by grind
  exact eq10842

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_pyy_pyx_pyy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq40 X0 (k X0 X0)
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq48
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq56
  have eq148 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq152 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       have j1 := eq58 X1 X0
       grind)
    | (have r₁ := eq148 X1 X0
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq148 X1 X1
       have r₂ := eq58 X1 X1
       grind)
    | exact resolve eq148 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq148
  have eq318 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq152 (σ X1) (σ X0)
       grind)
    | exact superpose eq152 eq15
    | exact resolve eq15 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq152 X1 X0
       grind)
    | exact superpose eq152 eq318
    | exact resolve eq318 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq318
  have eq327 : False := by grind
  exact eq327

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq43 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq49
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | exact resolve eq54 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq54
  have eq184 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq189 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq184 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq184 X1 X1
       have r₂ := eq56 X1 X1
       grind)
    | exact resolve eq184 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq184
  have eq232 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq189 (σ X1) (σ X0)
       grind)
    | exact superpose eq189 eq15
    | exact resolve eq15 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq232 X0 X1
       have i₂ := eq189 X1 X0
       grind)
    | exact superpose eq189 eq232
    | exact resolve eq232 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq232
  have eq239 : False := by grind
  exact eq239

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  clear eq25
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq38487 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38488 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq38487
    | exact resolve eq38487 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38487
  have eq38499 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq38488
       have r₂ := eq28
       grind)
    | exact resolve eq38488 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38488
  have eq38501 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq38499
    | exact resolve eq38499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38499
  have eq38544 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq38501 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq38501
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq38501
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq38501
       grind)
    | exact resolve eq12 eq38501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38501
  have eq38628 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq38544
  have eq38630 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq38628
       have r₂ := eq27
       grind)
    | exact resolve eq38628 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38628
  have eq38638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq38630 eq96
    | exact resolve eq96 eq38630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38630
  have eq38647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq38638
  have eq38650 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq38647
       have r₂ := eq28
       grind)
    | exact resolve eq38647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38647
  have eq38906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq38650
  have eq38995 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27 eq38906
    | exact resolve eq38906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38906
  have eq39002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq38995 eq96
    | exact resolve eq96 eq38995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq38995
  have eq39010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq39002
  have eq39012 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq39010
       have r₂ := eq28
       grind)
    | exact resolve eq39010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39010
  have eq39295 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq39012
       grind)
    | exact superpose eq39012 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq39012
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq39012
       grind)
    | exact resolve eq12 eq39012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39012
  have eq39379 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq39295
  have eq39381 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq39379
       have r₂ := eq19
       grind)
    | exact resolve eq39379 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39379
  have eq39385 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq39381
       grind)
    | exact superpose eq39381 eq73
    | exact resolve eq73 eq39381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39381
  have eq39405 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq39385
    | exact resolve eq39385 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39385
  have eq39420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39405 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq39405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq39420
    | exact resolve eq39420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39420
  have eq39436 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq39425
       have r₂ := eq28
       grind)
    | exact resolve eq39425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39425
  have eq39438 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq39436
    | exact resolve eq39436 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39436
  have eq44425 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39438 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq39438
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq39438
       grind)
    | exact resolve eq12 eq39438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39438
  have eq44510 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq44425
  have eq44512 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq44510
       have r₂ := eq27
       grind)
    | exact resolve eq44510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44510
  have eq44534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44512 eq39405
    | exact resolve eq39405 eq44512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44512
  have eq44537 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq44534
  have eq44548 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq44537
       have r₂ := eq28
       grind)
    | exact resolve eq44537 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44537
  have eq44571 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq44548
  have eq44661 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq44571
    | exact resolve eq44571 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44571
  have eq44682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq44661 eq39405
    | exact resolve eq39405 eq44661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39405 eq44661
  have eq44684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq44682
  have eq44694 : y = (M.op x x) := by
    first
    | (have r₁ := eq44684
       have r₂ := eq28
       grind)
    | exact resolve eq44684 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44684
  have eq44717 : (M.op x y) = (k y x) := by grind
  clear eq44694
  have eq44807 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq44717
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44717
    | exact resolve eq44717 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq44717
  have eq44810 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq44807
       grind)
    | exact superpose eq44807 eq73
    | exact resolve eq73 eq44807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq44807
  have eq44828 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq44810
    | exact resolve eq44810 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44810
  have eq45400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44828 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq44828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq45400
    | exact resolve eq45400 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45400
  have eq45412 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq45401
       have r₂ := eq28
       grind)
    | exact resolve eq45401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45401
  have eq45414 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq45412
    | exact resolve eq45412 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45412
  have eq51025 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45414 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq45414
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq45414
       grind)
    | exact resolve eq12 eq45414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45414
  have eq51113 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq51025
  have eq51115 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq51113
       have r₂ := eq27
       grind)
    | exact resolve eq51113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51113
  have eq51117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44828 eq51115
    | exact resolve eq51115 eq44828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51115
  have eq51119 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq51117
       have r₂ := eq28
       grind)
    | exact resolve eq51117 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51117
  have eq51141 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq51119
  have eq51234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44828 eq51141
    | exact resolve eq51141 eq44828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44828 eq51141
  have eq51236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq51234
    | exact resolve eq51234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq51234
  have eq51237 : False := by grind
  exact eq51237

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq57
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq87
  have eq400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq432 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq436 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq432 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq432 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq432 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq446 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       have j1 := eq81 X0 (σ X1)
       grind)
    | (have r₁ := eq436 X0 X1
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq436 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq436
  have eq454 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq446
    | (have j0 := eq446 X0 X1
       grind)
    | exact resolve eq446 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq455 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq454 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq459 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq455 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq455
    | exact resolve eq455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq455 x y
       grind)
    | exact superpose eq455 eq16
    | exact resolve eq16 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq567 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq459 X0 (τ X1)
       grind)
    | exact superpose eq459 eq17
    | exact resolve eq17 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq459
  have eq589 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq567
    | exact resolve eq567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq600 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq589
    | exact resolve eq589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq619 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq470
       have i₂ := eq600 x y
       grind)
    | exact superpose eq600 eq470
    | exact resolve eq470 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq600
  have eq620 : False := by grind
  exact eq620
