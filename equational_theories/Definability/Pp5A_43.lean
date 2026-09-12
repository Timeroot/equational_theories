import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq562
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq562
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1215 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1215
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1215
    | exact resolve eq1215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1226 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1224
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1224
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1224
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1224
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1224
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1224 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1224
  have eq1228 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1226
  have eq1304 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1228
       grind)
    | exact superpose eq1228 eq9
    | exact resolve eq9 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1305 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1304
  have eq1306 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1305
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1305
    | exact resolve eq1305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1307 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1306
  have eq1308 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1307
  have eq1386 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1308
       grind)
    | exact superpose eq1308 eq10
    | exact resolve eq10 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1388 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1386
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1386
    | exact resolve eq1386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1389 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1388
  have eq1392 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1389
       grind)
    | exact superpose eq1389 eq22
    | exact resolve eq22 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1439 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1392
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1392
    | exact resolve eq1392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1392
  have eq1461 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq568
       have i₂ := eq1439
       grind)
    | exact superpose eq1439 eq568
    | (have r₁ := eq568
       have r₂ := eq1439
       grind)
    | exact resolve eq568 eq1439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq1439
  have eq1464 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1461
  have eq1468 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1464
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1464
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1464
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1464
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1464
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1464 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1464
  have eq1469 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1468
  have eq1470 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1469
  have eq1472 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1470
       have r₂ := eq1389
       grind)
    | exact resolve eq1470 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq1470
  have eq1473 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1472
       grind)
    | exact superpose eq1472 eq9
    | exact resolve eq9 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1474 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1473
  have eq1475 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1474
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1474
    | exact resolve eq1474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474
  have eq1476 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1475
  have eq1477 : (σ x) = (σ y) := by grind
  clear eq1476
  have eq1479 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1477
       grind)
    | exact superpose eq1477 eq15
    | exact resolve eq15 eq1477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1526 : x = y := by
    first
    | (have i₁ := eq1479
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1479
    | exact resolve eq1479 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1529 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1526
       grind)
    | exact superpose eq1526 eq9
    | exact resolve eq9 eq1526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1530 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1529
  have eq1531 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1530
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1530
    | exact resolve eq1530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530
  have eq1532 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1531
  have eq1533 : False := by grind
  exact eq1533

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq2793 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2901 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2793 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793
  have eq2902 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2901 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901
  have eq3362 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2902 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq3365 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3362 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq3362 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq3362 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq3362 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X1 X1)
       grind)
    | exact resolve eq3362 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3474 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq3365 X0 (τ X1)
       grind)
    | exact superpose eq3365 eq19
    | (have j1 := eq3365 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3477 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3365 (σ X0) (σ X1)
       grind)
    | exact superpose eq3365 eq15
    | (have j1 := eq3365 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3569 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3474 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3474
    | exact resolve eq3474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474
  have eq3621 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3569 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3569
    | (have j0 := eq3569 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq3927 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3477 x y
       grind)
    | exact superpose eq3477 eq16
    | (have j1 := eq3477 x y
       grind)
    | exact resolve eq16 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477
  have eq3983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3927
       have i₂ := eq3621 y x
       grind)
    | exact superpose eq3621 eq3927
    | (have j1 := eq3621 (σ x) (σ y)
       grind)
    | (have r₁ := eq3927
       have r₂ := eq3621 y x
       grind)
    | (have r₁ := eq3927
       have r₂ := eq3621 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3927
       have r₂ := eq3621 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3927 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq3927
  have eq3984 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3983
  have eq3988 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3984
       grind)
    | exact superpose eq3984 eq10
    | exact resolve eq10 eq3984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3984
  have eq4032 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3988
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3988
    | exact resolve eq3988 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq4033 : x = y := by grind
  clear eq4032
  have eq4035 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4033
       grind)
    | exact superpose eq4033 eq16
    | exact resolve eq16 eq4033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4033
  have eq4036 : False := by grind
  exact eq4036

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq57 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X2) X2) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    grind
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq112 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq113 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq38
  have eq140 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq220 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq58 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq58
    | (have j0 := eq58 (σ x) (σ y)
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq237 : (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq220 eq223
    | exact resolve eq223 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq390 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 x y X1 X2
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59
    | (have j0 := eq59 X0 X1 X2 x y
       grind)
    | exact resolve eq59 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq461 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq114
    | (have j0 := eq114 (σ X0)
       grind)
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq114 x
       grind)
    | exact superpose eq114 eq44
    | (have j1 := eq114 x
       grind)
    | exact resolve eq44 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq390
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq390 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X0 X1) X2) X2) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq390 (M.op X0 X1) (M.op (M.op X0 X1) X2) X2
       grind)
    | exact superpose eq390 eq70
    | exact resolve eq70 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1290 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (k (M.op (M.op X0 X1) (M.op x y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1289 X0 X1 x
       have i₂ := eq729 (M.op X0 X1) x
       grind)
    | exact superpose eq729 eq1289
    | exact resolve eq1289 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729 eq1289
  have eq1299 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (k (M.op X0 (M.op X1 X2)) (M.op X0 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1290 X0 sF0
       have i₂ := eq14 X0 X1 X2 sF0
       grind)
    | exact superpose eq14 eq1290
    | exact resolve eq1290 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1332 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1299 X0 x x
       have i₂ := eq390 X0 x x
       grind)
    | (have i₁ := eq1299 X0 x y
       have i₂ := eq390 X0 x x
       grind)
    | exact superpose eq390 eq1299
    | (have j0 := eq1299 X0 x y
       grind)
    | exact resolve eq1299 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq1299
  have eq8798 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq14023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14023
    | exact resolve eq14023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14023
  have eq14035 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14024
       have r₂ := eq28
       grind)
    | exact resolve eq14024 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14024
  have eq14037 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14035
    | exact resolve eq14035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14035
  have eq14040 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14037 eq113
    | (have r₁ := eq113
       have r₂ := eq14037
       grind)
    | exact resolve eq113 eq14037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq14068 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq14037
  have eq14070 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq14040
  have eq14129 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14070
       have r₂ := eq14068
       grind)
    | exact resolve eq14070 eq14068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14068 eq14070
  have eq14135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14129 eq98
    | exact resolve eq98 eq14129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14129
  have eq14144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq14135
  have eq14147 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq14144
       have r₂ := eq28
       grind)
    | exact resolve eq14144 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144
  have eq14154 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq14147
  have eq14189 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq14154
    | exact resolve eq14154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14154
  have eq14200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq14189 eq98
    | exact resolve eq98 eq14189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq14189
  have eq14208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq14200
  have eq14210 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14208
       have r₂ := eq28
       grind)
    | exact resolve eq14208 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14208
  have eq14212 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq465
       have i₂ := eq14210
       grind)
    | exact superpose eq14210 eq465
    | exact resolve eq465 eq14210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14213 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq14210
       grind)
    | exact superpose eq14210 eq112
    | (have r₁ := eq112
       have r₂ := eq14210
       grind)
    | exact resolve eq112 eq14210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq14238 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq14210
  have eq14240 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq14213
  have eq14250 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq14212
    | exact resolve eq14212 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14212
  have eq14473 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14240
       have r₂ := eq14238
       grind)
    | exact resolve eq14240 eq14238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14238 eq14240
  have eq14625 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq77
       have i₂ := eq14473
       grind)
    | exact superpose eq14473 eq77
    | exact resolve eq77 eq14473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14473
  have eq14645 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq14625
    | exact resolve eq14625 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14625
  have eq14660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14645 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq14645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14660
    | exact resolve eq14660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14660
  have eq14676 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14665
       have r₂ := eq28
       grind)
    | exact resolve eq14665 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14665
  have eq14678 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14676
    | exact resolve eq14676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14676
  have eq14681 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq14250
       have i₂ := eq114 sF2
       grind)
    | exact superpose eq114 eq14250
    | (have j1 := eq114 (σ x)
       grind)
    | exact resolve eq14250 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq23488 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14678 eq14681
    | exact resolve eq14681 eq14678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14681
  have eq23534 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq23488
  have eq23544 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23534
       have r₂ := eq28
       grind)
    | exact resolve eq23534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23534
  have eq23915 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23544
  have eq23957 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq23915
    | exact resolve eq23915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23915
  have eq23984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23957 eq14645
    | exact resolve eq14645 eq23957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14645 eq23957
  have eq24014 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23984
  have eq24026 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24014
       have r₂ := eq28
       grind)
    | exact resolve eq24014 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24014
  have eq24029 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq465
       have i₂ := eq24026
       grind)
    | exact superpose eq24026 eq465
    | exact resolve eq465 eq24026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24032 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq24074 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24032
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24032
    | exact resolve eq24032 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24032
  have eq24075 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24029
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24029
    | exact resolve eq24029 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24029
  have eq24459 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq24074
       grind)
    | exact superpose eq24074 eq77
    | exact resolve eq77 eq24074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq24074
  have eq24478 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq24459
    | exact resolve eq24459 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24459
  have eq24942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24478 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq24478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24942
    | exact resolve eq24942 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24942
  have eq24956 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq24945
       have r₂ := eq28
       grind)
    | exact resolve eq24945 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24945
  have eq24958 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq24956
    | exact resolve eq24956 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24956
  have eq46843 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24958 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq24958
       grind)
    | exact resolve eq12 eq24958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46874 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24958
  have eq46875 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq46843
  have eq46876 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq46875
  have eq49820 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq46876 eq24075
    | exact resolve eq24075 eq46876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24075 eq46876
  have eq49824 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq49820
  have eq49834 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq49824
       have r₂ := eq46874
       grind)
    | exact resolve eq49824 eq46874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46874 eq49824
  have eq50157 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq49834
  have eq50202 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq50157
    | exact resolve eq50157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50157
  have eq50251 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq50202 eq24478
    | exact resolve eq24478 eq50202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24478 eq50202
  have eq50253 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq50251
  have eq50261 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq50253
       have r₂ := eq28
       grind)
    | exact resolve eq50253 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50253
  have eq50575 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50261 eq28
    | exact resolve eq28 eq50261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50576 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50261 eq220
    | exact resolve eq220 eq50261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq50596 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq50576
    | exact resolve eq50576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50576
  have eq50923 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50596 eq1332
    | exact resolve eq1332 eq50596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50596
  have eq51359 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq50261 eq50923
    | exact resolve eq50923 eq50261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50261 eq50923
  have eq51371 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq51359
  have eq51767 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq51371 eq50
    | exact resolve eq50 eq51371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51775 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq51371 eq14250
    | exact resolve eq14250 eq51371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14250 eq51371
  have eq51797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by grind
  clear eq51775
  have eq51804 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq51797
       have r₂ := eq50575
       grind)
    | exact resolve eq51797 eq50575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50575 eq51797
  have eq51811 : x = (k x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq51767
    | exact resolve eq51767 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq51767
  have eq52205 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq51804
       grind)
    | exact superpose eq51804 eq12
    | exact resolve eq12 eq51804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51804
  have eq52234 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) := by grind
  clear eq52205
  have eq52235 : y = (k x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq52234
  have eq52642 : x = y ∨ x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51811
       have i₂ := eq52235
       grind)
    | exact superpose eq52235 eq51811
    | exact resolve eq51811 eq52235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51811 eq52235
  have eq52646 : x = (M.op x y) ∨ x = y := by grind
  clear eq52642
  have eq52981 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq52646 eq21
    | exact resolve eq21 eq52646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52994 : (σ (k x x)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq52646 eq129
    | exact resolve eq129 eq52646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq53025 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq52646 eq206
    | exact resolve eq206 eq52646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq53183 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq53025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53025
    | exact resolve eq53025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53025
  have eq53214 : (k (σ x) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52994
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq52994
    | exact resolve eq52994 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52994
  have eq53227 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq52981
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52981
    | exact resolve eq52981 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52981
  have eq53791 : (k (M.op x y) x) = (M.op x (M.op x y)) ∨ x = y := by grind
  have eq54617 : (k x x) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = y := by
    first
    | exact superpose eq53214 eq50
    | exact resolve eq50 eq53214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53214
  have eq54651 : (k x x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq140 eq54617
    | exact resolve eq54617 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq54617
  have eq56038 : (k x x) = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52646 eq53791
    | exact resolve eq53791 eq52646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56048 : (k x x) = (M.op x x) ∨ x = y := by grind
  clear eq56038
  have eq57044 : (k x x) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq54651 eq53791
    | exact resolve eq53791 eq54651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53791 eq54651
  have eq57046 : (k x x) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq57044
  have eq59498 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq56048
       grind)
    | exact superpose eq56048 eq44
    | exact resolve eq44 eq56048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq56048
  have eq61006 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq59498
       have i₂ := eq53183
       grind)
    | exact superpose eq53183 eq59498
    | exact resolve eq59498 eq53183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53183 eq59498
  have eq61090 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq61006
  have eq61098 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq61090
    | exact resolve eq61090 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61090
  have eq61116 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq61098 eq50
    | exact resolve eq50 eq61098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq61150 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq31 eq61116
    | exact resolve eq61116 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61116
  have eq61901 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq57046
       have i₂ := eq61150
       grind)
    | exact superpose eq61150 eq57046
    | exact resolve eq57046 eq61150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57046
  have eq61902 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8798 x
       have i₂ := eq61150
       grind)
    | exact superpose eq61150 eq8798
    | (have j0 := eq8798 x
       grind)
    | exact resolve eq8798 eq61150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61150
  have eq61905 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq61901
  have eq61916 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq61902
    | exact resolve eq61902 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61902
  have eq61926 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq61916
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61916
    | exact resolve eq61916 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61916
  have eq61927 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq61926
       have r₂ := eq53227
       grind)
    | exact resolve eq61926 eq53227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53227 eq61926
  have eq61928 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq61927
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq61927
    | exact resolve eq61927 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61927
  have eq63370 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52646 eq61905
    | exact resolve eq61905 eq52646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61905
  have eq63443 : x = (M.op x x) ∨ x = y := by grind
  clear eq63370
  have eq63803 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq61928
  have eq71658 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq63803 eq61098
    | exact resolve eq61098 eq63803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61098 eq63803
  have eq71662 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq71658
  have eq71694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq71662 eq14678
    | exact resolve eq14678 eq71662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14678 eq71662
  have eq71755 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq71694
       have r₂ := eq28
       grind)
    | exact resolve eq71694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71694
  have eq85472 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63443
       have i₂ := eq71755
       grind)
    | exact superpose eq71755 eq63443
    | exact resolve eq63443 eq71755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63443 eq71755
  have eq85513 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq85472
  have eq85548 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq85513 eq30
    | exact resolve eq30 eq85513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq85513
  have eq85741 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq85548
    | exact resolve eq85548 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq85548
  have eq86014 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq85741 eq52646
    | exact resolve eq52646 eq85741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52646 eq85741
  have eq86121 : x = y := by grind
  clear eq86014
  have eq86406 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq86121
       grind)
    | exact superpose eq86121 eq19
    | exact resolve eq19 eq86121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq86407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq86121
       grind)
    | exact superpose eq86121 eq25
    | exact resolve eq25 eq86121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq86733 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq86407
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq86407
    | exact resolve eq86407 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86407
  have eq86735 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq86733 eq27
    | exact resolve eq27 eq86733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq86733
  have eq86959 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq465
       have i₂ := eq86406
       grind)
    | exact superpose eq86406 eq465
    | exact resolve eq465 eq86406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq86963 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24026
       have i₂ := eq86406
       grind)
    | exact superpose eq86406 eq24026
    | exact resolve eq24026 eq86406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24026
  have eq86977 : (k (M.op x y) x) = (M.op x (M.op x y)) := by grind
  have eq87029 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq86963
       have i₂ := eq86121
       grind)
    | exact superpose eq86121 eq86963
    | exact resolve eq86963 eq86121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86121 eq86963
  have eq87030 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq87029
  have eq87033 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq86959
    | exact resolve eq86959 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86959
  have eq87138 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87030 eq28
    | exact resolve eq28 eq87030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87141 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87030 eq237
    | exact resolve eq237 eq87030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq87175 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq86735 eq87141
    | exact resolve eq87141 eq86735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87141
  have eq92064 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87175 eq1332
    | exact resolve eq1332 eq87175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq87175
  have eq93688 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq87030 eq92064
    | exact resolve eq92064 eq87030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87030 eq92064
  have eq93704 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq93688
  have eq96081 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq93704 eq87033
    | exact resolve eq87033 eq93704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87033 eq93704
  have eq96091 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq96081
  have eq96111 : x = (M.op x y) := by
    first
    | (have r₁ := eq96091
       have r₂ := eq87138
       grind)
    | exact resolve eq96091 eq87138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87138 eq96091
  have eq97075 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq96111 eq21
    | exact resolve eq21 eq96111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq97308 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq96111 eq86977
    | exact resolve eq86977 eq96111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86977
  have eq97315 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq97308
       have i₂ := eq86406
       grind)
    | exact superpose eq86406 eq97308
    | exact resolve eq97308 eq86406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86406 eq97308
  have eq97478 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97075
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq97075
    | exact resolve eq97075 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97075
  have eq97481 : x = (k x x) := by
    first
    | exact superpose eq96111 eq97315
    | exact resolve eq97315 eq96111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96111 eq97315
  have eq98213 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8798 x
       have i₂ := eq97481
       grind)
    | exact superpose eq97481 eq8798
    | (have j0 := eq8798 x
       grind)
    | exact resolve eq8798 eq97481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8798 eq97481
  have eq98218 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq98213
  have eq98231 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98218
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq98218
    | exact resolve eq98218 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq98218
  have eq98249 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86735 eq98231
    | exact resolve eq98231 eq86735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86735 eq98231
  have eq98266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq97478 eq98249
    | exact resolve eq98249 eq97478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97478 eq98249
  have eq98281 : False := by grind
  exact eq98281

/-- `Equation4533`: `x ◇ (y ◇ z) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_x_pxx_pxy_Equation4533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X2) := by
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 X2) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X3 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have r₂ := eq16 (M.op (M.op X1 X2) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq16 (M.op (M.op X0 X1) X1) X0 X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq188 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq179 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op (M.op x y) y)
       have r₂ := eq179 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq179 eq188
    | exact resolve eq188 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq195 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq196
    | exact resolve eq196 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq196
  have eq252 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq193 eq16
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq276 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq201 eq16
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq528 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) ∨ y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq252
       have i₂ := eq11 (M.op sF0 y) y
       grind)
    | exact superpose eq11 eq252
    | (have j1 := eq11 (M.op (M.op x y) y) y
       grind)
    | exact resolve eq252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq559 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq276
       have i₂ := eq11 (M.op sF4 sF3) sF3
       grind)
    | exact superpose eq11 eq276
    | (have j1 := eq11 (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq572 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have j1 := eq183 (M.op (σ x) (σ y)) (σ y) (σ y)
       grind)
    | (have r₁ := eq559
       have r₂ := eq183 (σ x) (σ y) (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))
       grind)
    | (have r₁ := eq559
       have r₂ := eq183 (M.op (σ x) (σ y)) (σ y) (σ y)
       grind)
    | exact resolve eq559 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq588 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) ∨ y = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have j1 := eq183 (M.op x y) y y
       grind)
    | (have r₁ := eq558
       have r₂ := eq183 x y (k (M.op (M.op x y) y) y)
       grind)
    | (have r₁ := eq558
       have r₂ := eq183 (M.op x y) y y
       grind)
    | exact resolve eq558 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq558
  have eq598 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | (have j1 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)
       grind)
    | (have r₁ := eq587
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)
       grind)
    | exact resolve eq587 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq599 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | (have j1 := eq13 (M.op (M.op x y) y) y
       grind)
    | (have r₁ := eq588
       have r₂ := eq13 (M.op (M.op x y) y) y
       grind)
    | exact resolve eq588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq803 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (M.op (σ x) (σ y)) (σ y))) y) := by
    first
    | exact superpose eq598 eq152
    | exact resolve eq152 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq598
  have eq1241 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1273 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have j0 := eq189 (M.op (M.op x y) y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1276 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq179 eq1273
    | exact resolve eq1273 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1291 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1276 eq37
    | exact resolve eq37 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1276
  have eq1292 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq1291
    | (have j0 := eq1291 X0
       grind)
    | exact resolve eq1291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1560 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 X4 (M.op X1 X2)
       have i₂ := eq181 (M.op X4 (M.op X1 X2)) X1 X2 X0
       grind)
    | (have i₁ := eq16 X3 X4 (M.op X1 X2)
       have i₂ := eq181 X0 X1 X2 (M.op X4 (M.op X1 X2))
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2439 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq528
       grind)
    | exact superpose eq528 eq40
    | exact resolve eq40 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2440 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2439
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2439
    | exact resolve eq2439 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2442 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2440
    | exact resolve eq2440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq2788 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) ≠ (M.op X0 (M.op X1 (M.op X2 X3))) ∨ (k X3 (M.op X1 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X1 (M.op X2 X3))
       have i₂ := eq178 X1 X2 X3 X0
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 (M.op X1 (M.op X2 X3))
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X2)
       have r₂ := eq178 X0 X1 X2 (M.op (M.op X0 (M.op X1 X2)) X2)
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2912 : ∀ X1 X2 X3 : G, (k X3 (M.op X1 (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have j0 := eq2788 x X1 X2 X3
       grind)
    | (have r₁ := eq2788 X3 x X1 X2
       have r₂ := eq1560 x X1 X2 X3 x
       grind)
    | exact resolve eq2788 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560 eq2788
  have eq3154 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2912 x (M.op X0 X1) X1
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq2912
    | exact resolve eq2912 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912
  have eq3325 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op (M.op X0 x) x)
       have i₂ := eq3154 X0 x
       grind)
    | exact superpose eq3154 eq35
    | exact resolve eq35 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3329 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op (M.op X0 sF2) sF2)
       have i₂ := eq3154 X0 sF2
       grind)
    | exact superpose eq3154 eq90
    | exact resolve eq90 eq3154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3154
  have eq3332 : ∀ X0 : G, x = (k x (τ (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq29 eq3329
    | exact resolve eq3329 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329
  have eq3336 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | (have i₁ := eq3325 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3325
    | (have j0 := eq3325 X0
       grind)
    | exact resolve eq3325 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq4912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2442 eq530
    | exact resolve eq530 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq4921 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq4912
       have r₂ := eq27
       grind)
    | exact resolve eq4912 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4912
  have eq4926 : x = (k x (τ (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4921 eq3332
    | exact resolve eq3332 eq4921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq4950 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4921 eq4926
    | exact resolve eq4926 eq4921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921 eq4926
  have eq4954 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq4950
    | exact resolve eq4950 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq4957 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq4954
       have r₂ := eq13 x y
       grind)
    | exact resolve eq4954 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4954
  have eq4959 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq528
       have i₂ := eq4957
       grind)
    | exact superpose eq4957 eq528
    | exact resolve eq528 eq4957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq4957
  have eq4963 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4959
  have eq5000 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq185 y x x
       have i₂ := eq4963
       grind)
    | exact superpose eq4963 eq185
    | exact resolve eq185 eq4963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq5009 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4963 eq5000
    | exact resolve eq5000 eq4963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963 eq5000
  have eq5141 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5009 x
       grind)
    | exact superpose eq5009 eq18
    | (have j1 := eq5009 x
       grind)
    | exact resolve eq18 eq5009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5009
  have eq5158 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5141
  have eq5170 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5158 eq195
    | exact resolve eq195 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5303 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5170 eq26
    | (have j1 := eq5170 X0 (σ x)
       grind)
    | exact resolve eq26 eq5170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5170
  have eq5329 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5158 eq5303
    | exact resolve eq5303 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158 eq5303
  have eq5417 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5329 eq803
    | exact resolve eq803 eq5329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5329
  have eq5428 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq5417
    | exact resolve eq5417 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5417
  have eq5463 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq572 y y
       have i₂ := eq5428
       grind)
    | exact superpose eq5428 eq572
    | (have j0 := eq572 y y
       grind)
    | (have r₁ := eq572 y y
       have r₂ := eq5428
       grind)
    | exact resolve eq572 eq5428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq5464 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5463
  have eq5465 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5464
  have eq5475 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 y y x
       have i₂ := eq5465
       grind)
    | exact superpose eq5465 eq181
    | exact resolve eq181 eq5465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5629 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq5475 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq5475 x X0
       grind)
    | exact superpose eq5475 eq18
    | (have j1 := eq5475 X0 x
       grind)
    | exact resolve eq18 eq5475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475
  have eq5722 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5465
       have i₂ := eq5629 y
       grind)
    | exact superpose eq5629 eq5465
    | exact resolve eq5465 eq5629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5465 eq5629
  have eq5741 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5722
  have eq5756 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5741
       grind)
    | exact superpose eq5741 eq18
    | exact resolve eq18 eq5741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5757 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5741
       grind)
    | exact superpose eq5741 eq24
    | exact resolve eq24 eq5741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5804 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5757
    | exact resolve eq5757 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5757
  have eq5805 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179 eq5756
    | exact resolve eq5756 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756
  have eq5806 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5741 eq5805
    | exact resolve eq5805 eq5741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5741 eq5805
  have eq5865 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5806 eq1292
    | exact resolve eq1292 eq5806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292 eq5806
  have eq5889 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5865
    | exact resolve eq5865 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5865
  have eq5902 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5804 eq5889
    | exact resolve eq5889 eq5804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5889
  have eq6299 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5902 eq572
    | (have j0 := eq572 (σ y) (σ y)
       grind)
    | (have r₁ := eq572 (σ y) (σ y)
       have r₂ := eq5902
       grind)
    | exact resolve eq572 eq5902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902
  have eq6300 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6299
  have eq6301 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6300
  have eq6320 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6301 eq181
    | exact resolve eq181 eq6301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6464 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6320 eq26
    | (have j1 := eq6320 X0 (σ x)
       grind)
    | exact resolve eq26 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6465 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6320 eq6301
    | exact resolve eq6301 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301 eq6320
  have eq6480 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6465 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6465
  have eq6504 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6480 eq6464
    | (have j1 := eq6480 (σ x)
       grind)
    | exact resolve eq6464 eq6480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6464 eq6480
  have eq6530 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6504 eq27
    | exact resolve eq27 eq6504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504
  have eq6570 : x = (M.op x y) := by
    first
    | (have r₁ := eq6530
       have r₂ := eq5804
       grind)
    | exact resolve eq6530 eq5804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5804 eq6530
  have eq6573 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6570
       grind)
    | exact superpose eq6570 eq18
    | exact resolve eq18 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6574 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6570
       grind)
    | exact superpose eq6570 eq22
    | exact resolve eq22 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6582 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 (M.op x y)) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3336 X0
       have i₂ := eq6570
       grind)
    | exact superpose eq6570 eq3336
    | exact resolve eq3336 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq6590 : (σ x) = (k (σ x) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq179 eq6582
    | exact resolve eq6582 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq6582
  have eq6593 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq6573 eq6590
    | exact resolve eq6590 eq6573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590
  have eq6595 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6593
    | exact resolve eq6593 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6593
  have eq6598 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6574 eq20
    | exact resolve eq20 eq6574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6609 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq6574 eq1241
    | exact resolve eq1241 eq6574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq7270 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq6573 eq599
    | exact resolve eq599 eq6573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq7336 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq6595 eq572
    | (have j0 := eq572 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq572 eq6595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6595
  have eq7338 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq7336
       have r₂ := eq6598
       grind)
    | exact resolve eq7336 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336
  have eq7344 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq6598 eq7338
    | exact resolve eq7338 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7338
  have eq7349 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6598 eq7344
    | exact resolve eq7344 eq6598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq7350 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7349
  have eq7539 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq7350 eq181
    | exact resolve eq181 eq7350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7633 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq7539 eq7350
    | exact resolve eq7350 eq7539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7350 eq7539
  have eq8941 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq530 eq6609
    | exact resolve eq6609 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq6609
  have eq9004 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq31 eq8941
    | exact resolve eq8941 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8941
  have eq9034 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq7270 eq9004
    | exact resolve eq9004 eq7270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7270 eq9004
  have eq9054 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7633 eq9034
    | exact resolve eq9034 eq7633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9034
  have eq9759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9054 eq14
    | exact resolve eq14 eq9054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9054
  have eq9770 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9759
    | exact resolve eq9759 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9759
  have eq9775 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9770
       have r₂ := eq27
       grind)
    | exact resolve eq9770 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770
  have eq9781 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq9775 eq195
    | exact resolve eq195 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq9967 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq9781 eq26
    | (have j1 := eq9781 X0 (σ x)
       grind)
    | exact resolve eq26 eq9781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9781
  have eq9994 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq9775 eq9967
    | exact resolve eq9967 eq9775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9775 eq9967
  have eq10100 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9994 eq803
    | exact resolve eq803 eq9994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq9994
  have eq10112 : y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq10100
    | exact resolve eq10100 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10100
  have eq10151 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq572 y y
       have i₂ := eq10112
       grind)
    | exact superpose eq10112 eq572
    | (have j0 := eq572 y y
       grind)
    | (have r₁ := eq572 y y
       have r₂ := eq10112
       grind)
    | exact resolve eq572 eq10112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq10112
  have eq10152 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq10151
  have eq10153 : y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq10152
  have eq10171 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 y y x
       have i₂ := eq10153
       grind)
    | exact superpose eq10153 eq181
    | exact resolve eq181 eq10153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq10373 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10153
       have i₂ := eq10171 X0 y
       grind)
    | (have i₁ := eq10153
       have i₂ := eq10171 y X0
       grind)
    | exact superpose eq10171 eq10153
    | exact resolve eq10153 eq10171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10153
  have eq10392 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6573
       have i₂ := eq10171 X0 sF0
       grind)
    | (have i₁ := eq6573
       have i₂ := eq10171 sF0 x
       grind)
    | exact superpose eq10171 eq6573
    | (have j1 := eq10171 X0 x
       grind)
    | exact resolve eq6573 eq10171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6573 eq10171
  have eq10393 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq10373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10373
  have eq10413 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10392 eq10393
    | (have j0 := eq10393 x
       grind)
    | exact resolve eq10393 eq10392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10392 eq10393
  have eq10496 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10413 eq31
    | exact resolve eq31 eq10413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq10413
  have eq10610 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq10496
    | exact resolve eq10496 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10496
  have eq10634 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10610
       have i₂ := eq6570
       grind)
    | exact superpose eq6570 eq10610
    | exact resolve eq10610 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6570 eq10610
  have eq10635 : y = (M.op x y) := by grind
  clear eq10634
  have eq10651 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10635
       grind)
    | exact superpose eq10635 eq24
    | exact resolve eq24 eq10635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10635
  have eq10705 : (σ x) = (σ y) := by
    first
    | exact superpose eq6574 eq10651
    | exact resolve eq10651 eq6574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6574 eq10651
  have eq10706 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10705 eq26
    | exact resolve eq26 eq10705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10705
  have eq10812 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7633 eq10706
    | exact resolve eq10706 eq7633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7633 eq10706
  have eq11396 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq10812 eq27
    | exact resolve eq27 eq10812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10812
  have eq11467 : False := by grind
  exact eq11467

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pyx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq42
    | exact resolve eq42 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq42
  have eq87 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq100 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq47 X1
       grind)
    | exact superpose eq47 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3577 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq100 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq100 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq100 X0 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq100 X1 X1
       grind)
    | exact resolve eq12 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3578 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq100 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq13
    | (have j1 := eq100 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq100 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq100 X0 X1
       grind)
    | exact resolve eq13 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq3637 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3578 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578
  have eq3646 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3637 X0 X1
       have j1 := eq87 X1 (σ X0)
       grind)
    | (have r₁ := eq3637 X0 X0
       have r₂ := eq87 X0 (σ X0)
       grind)
    | exact resolve eq3637 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3647 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3577 X0 X1
       have j1 := eq87 X1 (σ X0)
       grind)
    | (have r₁ := eq3577 X0 X0
       have r₂ := eq87 X0 (σ X0)
       grind)
    | exact resolve eq3577 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq3577
  have eq3658 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3646 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3646
    | (have j0 := eq3646 X0 X1
       grind)
    | exact resolve eq3646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq3659 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3658
  have eq3660 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3647 X0 X1
       have i₂ := eq47 X1
       grind)
    | exact superpose eq47 eq3647
    | (have j0 := eq3647 X0 X1
       grind)
    | exact resolve eq3647 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq3668 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3659 X0 X1
       have i₂ := eq47 X1
       grind)
    | exact superpose eq47 eq3659
    | (have j0 := eq3659 X0 X1
       grind)
    | exact resolve eq3659 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3659
  have eq3669 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3660 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3660
    | (have j0 := eq3660 X0 X1
       grind)
    | exact resolve eq3660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660
  have eq3670 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3669 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3669
  have eq3673 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3670 X0 X1
       have j1 := eq3668 X0 X1
       grind)
    | (have r₁ := eq3670 X0 X1
       have r₂ := eq3668 X0 X1
       grind)
    | exact resolve eq3670 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668 eq3670
  have eq3676 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3673 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3673
    | exact resolve eq3673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3690 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3673 x y
       grind)
    | exact superpose eq3673 eq16
    | exact resolve eq16 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq3955 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq3676 X0 (τ X1)
       grind)
    | exact superpose eq3676 eq17
    | exact resolve eq17 eq3676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3676
  have eq3991 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3955 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3955
    | exact resolve eq3955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq4008 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3991 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3991
    | exact resolve eq3991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq4045 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3690
       have i₂ := eq4008 x y
       grind)
    | exact superpose eq4008 eq3690
    | exact resolve eq3690 eq4008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3690 eq4008
  have eq4046 : False := by grind
  exact eq4046

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_y_pxx_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq86 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq81 sF2 x
       grind)
    | exact superpose eq81 eq58
    | exact resolve eq58 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq108 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq119 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 X1) x
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq92 (M.op x y) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 sF0 X1
       have i₂ := eq9 sF0 x x
       grind)
    | (have i₁ := eq119 x X1
       have i₂ := eq9 x sF0 x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq81 sF0 x
       grind)
    | exact superpose eq81 eq134
    | exact resolve eq134 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq153 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq153 (σ X0)
       grind)
    | exact superpose eq153 eq15
    | exact resolve eq15 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq174
    | exact resolve eq174 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq174
  have eq196 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq94 eq108
    | exact resolve eq108 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq196
       have i₂ := eq57 sF0 sF2 sF2
       grind)
    | exact superpose eq57 eq196
    | exact resolve eq196 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq217 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq108 eq209
    | exact resolve eq209 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq230 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq217 eq9
    | exact resolve eq9 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op x X0)
       have i₂ := eq81 (M.op x X0) X0
       grind)
    | (have i₁ := eq175 (M.op x y)
       have i₂ := eq81 (M.op x y) x
       grind)
    | exact superpose eq81 eq175
    | exact resolve eq175 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq10
    | exact resolve eq10 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq139 eq324
    | exact resolve eq324 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq324
  have eq340 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq175 sF0
       grind)
    | exact superpose eq175 eq338
    | exact resolve eq338 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq341 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq340
    | (have j0 := eq340 X0
       grind)
    | exact resolve eq340 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq375 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq327 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq327
    | exact resolve eq327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq447 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (τ (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | exact superpose eq217 eq375
    | exact resolve eq375 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq483 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq483
    | exact resolve eq483 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq489 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq487
    | exact resolve eq487 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq491 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq489
    | exact resolve eq489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq521 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (σ x) (σ y)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq108 eq52
    | exact resolve eq52 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq94 eq52
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq556 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X0 X2 X1
       grind)
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X1 X2 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq565 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq528
    | exact resolve eq528 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq583 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X3) = (M.op (M.op X3 X4) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq565 X0 x X2 X3 X4
       have i₂ := eq521 X0 x (M.op X0 X2) X3
       grind)
    | (have i₁ := eq565 (σ x) (σ y) X2 X3 X4
       have i₂ := eq521 (M.op (σ x) X2) x X2 X3
       grind)
    | exact superpose eq521 eq565
    | exact resolve eq565 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521 eq565
  have eq605 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq577 eq230
    | exact resolve eq230 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq607 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq577 eq583
    | exact resolve eq583 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq583
  have eq1141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq605 eq52
    | exact resolve eq52 eq605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq2105 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op X0 X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq175
    | exact resolve eq175 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2209 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2105 X0
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq2105
    | exact resolve eq2105 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2272 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) X0) X0)) = (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2209 X0
       have i₂ := eq607 (σ X0) (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq607 eq2209
    | exact resolve eq2209 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2856 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 (M.op X0 X1)
       have i₂ := eq607 X0 X1 X0 X1
       grind)
    | (have i₁ := eq375 (M.op (M.op x y) (M.op x y))
       have i₂ := eq607 X0 x (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact superpose eq607 eq375
    | exact resolve eq375 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2882 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op x y) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq607 eq52
    | exact resolve eq52 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3468 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq341 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq341
    | exact resolve eq341 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq3509 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq3468
       have i₂ := eq607 (σ x) (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq607 eq3468
    | exact resolve eq3468 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq3468
  have eq3521 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3509
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3509
    | exact resolve eq3509 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3509
  have eq3527 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq108 eq3521
    | exact resolve eq3521 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521
  have eq3537 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3527 eq447
    | exact resolve eq447 eq3527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447 eq3527
  have eq3557 : (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3537
       have i₂ := eq375 sF1
       grind)
    | exact superpose eq375 eq3537
    | exact resolve eq3537 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537
  have eq3563 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq37 eq3557
    | exact resolve eq3557 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3557
  have eq4088 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq3563 eq556
    | exact resolve eq556 eq3563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7574 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4088 eq1141
    | exact resolve eq1141 eq4088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq7581 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4088 eq52
    | exact resolve eq52 eq4088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq4088
  have eq12503 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2272 x
       have i₂ := eq556 sF0 x x x
       grind)
    | (have i₁ := eq2272 X0
       have i₂ := eq556 X0 X1 sF0 X0
       grind)
    | exact superpose eq556 eq2272
    | exact resolve eq2272 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq12531 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq2272 eq10
    | exact resolve eq10 eq2272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq18222 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X1 X2)) (τ (M.op X1 X2))) = (τ (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375 (M.op X1 X2)
       have i₂ := eq2882 X1 X2 X1 X2 X0
       grind)
    | (have i₁ := eq375 (M.op (M.op x y) x)
       have i₂ := eq2882 (M.op (M.op x y) x) X1 X2 x x
       grind)
    | exact superpose eq2882 eq375
    | exact resolve eq375 eq2882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq2882
  have eq23356 : ∀ X0 : G, (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (M.op (M.op x y) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq12531 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12531
    | exact resolve eq12531 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531
  have eq23416 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (τ X0)) = (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq23356 X0
       have i₂ := eq57 sF0 (τ X0) (τ X0)
       grind)
    | exact superpose eq57 eq23356
    | exact resolve eq23356 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq23356
  have eq23440 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (M.op (M.op (M.op x y) (M.op x y)) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq23416 eq2856
    | exact resolve eq2856 eq23416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856 eq23416
  have eq23476 : ∀ X0 X1 : G, (τ (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op x y) (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18222 X0 X1 x
       have i₂ := eq23440 X1 x
       grind)
    | exact superpose eq23440 eq18222
    | exact resolve eq18222 eq23440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18222 eq23440
  have eq61939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq491
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq491
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq491 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61972 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq61939
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61939
    | exact resolve eq61939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61939
  have eq61981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq61972
    | exact resolve eq61972 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61972
  have eq61982 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq61981
       have r₂ := eq27
       grind)
    | exact resolve eq61981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61981
  have eq61983 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq61982
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61982
    | exact resolve eq61982 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61982
  have eq61984 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq61983
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61983
    | exact resolve eq61983 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61983
  have eq61992 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq61984 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq61984
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq61984
       grind)
    | exact resolve eq12 eq61984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61984
  have eq66474 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq61992
    | (have j0 := eq61992 (σ x)
       grind)
    | (have r₁ := eq61992 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq61992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61992
  have eq66480 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq66474
  have eq66486 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq61 eq66480
    | exact resolve eq66480 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq66480
  have eq66499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66486
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq66486
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq66486 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66486
  have eq66536 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66499
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66499
    | exact resolve eq66499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66499
  have eq66545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq66536
    | exact resolve eq66536 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66536
  have eq66546 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq66545
       have r₂ := eq27
       grind)
    | exact resolve eq66545 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66545
  have eq66547 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66546
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66546
    | exact resolve eq66546 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66546
  have eq66548 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq66547
  have eq66549 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq66548
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66548
    | exact resolve eq66548 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66548
  have eq66550 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66549
  have eq66552 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq66550
       grind)
    | exact superpose eq66550 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq66550
       grind)
    | exact resolve eq12 eq66550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66558 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq66550
       grind)
    | exact superpose eq66550 eq175
    | exact resolve eq175 eq66550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq66550
  have eq66691 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66558
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq66558
    | exact resolve eq66558 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66558
  have eq66721 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq66691
    | exact resolve eq66691 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66691
  have eq75305 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66552 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66552
    | (have j0 := eq66552 x
       grind)
    | (have r₁ := eq66552 x
       have r₂ := eq18
       grind)
    | exact resolve eq66552 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66552
  have eq75315 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq75305
  have eq75335 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq491
       have i₂ := eq75315
       grind)
    | exact superpose eq75315 eq491
    | exact resolve eq491 eq75315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq75315
  have eq75341 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq75335
  have eq75346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq75341
    | exact resolve eq75341 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75341
  have eq75350 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75346
       have r₂ := eq27
       grind)
    | exact resolve eq75346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75346
  have eq75382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75350 eq66721
    | exact resolve eq66721 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66721 eq75350
  have eq75490 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq75382
  have eq75558 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq75490
       have r₂ := eq27
       grind)
    | exact resolve eq75490 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75490
  have eq75614 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75558 eq3563
    | exact resolve eq3563 eq75558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq75626 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq75558 eq7574
    | exact resolve eq7574 eq75558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7574
  have eq75627 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X2) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq75558 eq7581
    | exact resolve eq7581 eq75558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7581
  have eq75663 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X2) x) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq38 eq75627
    | exact resolve eq75627 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75627
  have eq75664 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) x) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq38 eq75626
    | exact resolve eq75626 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75626
  have eq75674 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq75614
    | exact resolve eq75614 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75614
  have eq75688 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq75663 X0 X1 x
       have i₂ := eq92 X1 x
       grind)
    | (have i₁ := eq75663 X0 x y
       have i₂ := eq92 x X1
       grind)
    | exact superpose eq92 eq75663
    | exact resolve eq75663 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75663
  have eq75689 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq75664 X0 X1 x
       have i₂ := eq92 X0 x
       grind)
    | (have i₁ := eq75664 x X1 y
       have i₂ := eq92 x X1
       grind)
    | exact superpose eq92 eq75664
    | exact resolve eq75664 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75664
  have eq75695 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq108 eq75689
    | exact resolve eq75689 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq75689
  have eq80348 : ∀ X0 : G, (M.op (M.op x x) (τ X0)) = (τ (M.op (M.op x x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75674 eq23476
    | exact resolve eq23476 eq75674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23476 eq75674
  have eq80553 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x x) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq80348 X0
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq80348
    | exact resolve eq80348 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80348
  have eq80645 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x y) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq80553 X0
       have i₂ := eq81 (τ X0) x
       grind)
    | exact superpose eq81 eq80553
    | exact resolve eq80553 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80553
  have eq80706 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq75558 eq75695
    | exact resolve eq75695 eq75558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75695
  have eq80877 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq80706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80706
  have eq82034 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80877 eq26
    | (have j1 := eq80877 (σ y)
       grind)
    | exact resolve eq26 eq80877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80877
  have eq100781 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq82034 eq80645
    | exact resolve eq80645 eq82034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80645 eq82034
  have eq100823 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ x = (M.op x y) := by grind
  clear eq100781
  have eq100848 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq100823
    | exact resolve eq100823 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq100823
  have eq100905 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq75558 eq100848
    | exact resolve eq100848 eq75558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75558 eq100848
  have eq100953 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq100905
  have eq100955 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq100953
    | exact resolve eq100953 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq100953
  have eq100988 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq100955 eq75688
    | exact resolve eq75688 eq100955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75688
  have eq101098 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq100988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100988
  have eq104450 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq101098 eq100955
    | exact resolve eq100955 eq101098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100955 eq101098
  have eq104643 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq104450
  have eq104806 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104643
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104643
    | exact resolve eq104643 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104643
  have eq104807 : x = (M.op x y) := by grind
  clear eq104806
  have eq104945 : x = (M.op x y) := by
    first
    | exact superpose eq104807 eq18
    | exact resolve eq18 eq104807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq104946 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq104807 eq20
    | exact resolve eq20 eq104807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq104954 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq104807 eq81
    | exact resolve eq81 eq104807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq104955 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq104807 eq92
    | exact resolve eq92 eq104807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105311 : ∀ X0 X1 : G, (M.op (M.op x x) (σ X0)) = (σ (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | exact superpose eq104807 eq12503
    | exact resolve eq12503 eq104807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503 eq104807
  have eq107611 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op x x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105311 X0 x
       have i₂ := eq104955 X0 x
       grind)
    | exact superpose eq104955 eq105311
    | exact resolve eq105311 eq104955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104955 eq105311
  have eq107958 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq104946
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq104946
    | exact resolve eq104946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104946
  have eq108774 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq107611 X0
       have i₂ := eq104954 (σ X0) x
       grind)
    | exact superpose eq104954 eq107611
    | exact resolve eq107611 eq104954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107611
  have eq109098 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq107958 eq22
    | exact resolve eq22 eq107958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq109099 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq107958 eq26
    | exact resolve eq26 eq107958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq107958
  have eq112953 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq108774 y
       have i₂ := eq104945
       grind)
    | exact superpose eq104945 eq108774
    | exact resolve eq108774 eq104945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104945 eq108774
  have eq113001 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq112953
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq112953
    | exact resolve eq112953 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq112953
  have eq113018 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq113001
       have i₂ := eq109098
       grind)
    | exact superpose eq109098 eq113001
    | exact resolve eq113001 eq109098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109098 eq113001
  have eq113071 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq113018 eq104954
    | exact resolve eq104954 eq113018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104954
  have eq113151 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq113071 eq109099
    | exact resolve eq109099 eq113071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109099 eq113071
  have eq113168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq113018 eq113151
    | exact resolve eq113151 eq113018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113018 eq113151
  have eq113226 : False := by grind
  exact eq113226

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq50
    | exact resolve eq50 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq76
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq76
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq103
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq118
    | exact resolve eq118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq119
    | exact resolve eq119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq43571 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq43571
    | exact resolve eq43571 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43571
  have eq43583 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq43572
       have r₂ := eq28
       grind)
    | exact resolve eq43572 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43572
  have eq43587 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq43583
    | exact resolve eq43583 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43583
  have eq43591 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq43587 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq43587
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq43587
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43587
       grind)
    | exact resolve eq13 eq43587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43587
  have eq43692 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq43591
       have r₂ := eq27
       grind)
    | exact resolve eq43591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43591
  have eq43730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq43692 eq120
    | exact resolve eq120 eq43692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq43692
  have eq43739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq43730
  have eq43742 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq43739
       have r₂ := eq28
       grind)
    | exact resolve eq43739 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43739
  have eq43746 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq43742
       grind)
    | exact superpose eq43742 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq43742
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq43742
       grind)
    | exact resolve eq13 eq43742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43742
  have eq43822 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq43746
       have r₂ := eq19
       grind)
    | exact resolve eq43746 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43746
  have eq43841 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq43822
       grind)
    | exact superpose eq43822 eq103
    | exact resolve eq103 eq43822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq43822
  have eq43857 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq43841
    | exact resolve eq43841 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43841
  have eq43894 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43857 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq43857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43895 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq43894
  have eq43899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq43895
    | exact resolve eq43895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43895
  have eq43910 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq43899
       have r₂ := eq28
       grind)
    | exact resolve eq43899 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43899
  have eq43914 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq43910
    | exact resolve eq43910 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43910
  have eq43944 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq43914 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq43914
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq43914
       grind)
    | exact resolve eq13 eq43914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43914
  have eq44045 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq43944
       have r₂ := eq27
       grind)
    | exact resolve eq43944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43944
  have eq44091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq44045 eq43857
    | exact resolve eq43857 eq44045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43857 eq44045
  have eq44094 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq44091
  have eq44099 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq44094
       have r₂ := eq28
       grind)
    | exact resolve eq44094 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44094
  have eq44105 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq44099 eq30
    | exact resolve eq30 eq44099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq44099
  have eq44209 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq44105
    | exact resolve eq44105 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44105
  have eq44210 : x = y := by grind
  clear eq44209
  have eq44231 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq44210
       grind)
    | exact superpose eq44210 eq19
    | exact resolve eq19 eq44210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq44232 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq44210
       grind)
    | exact superpose eq44210 eq25
    | exact resolve eq25 eq44210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq44210
  have eq44333 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq44232
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44232
    | exact resolve eq44232 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44232
  have eq44354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq44333 eq27
    | exact resolve eq27 eq44333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq44333
  have eq44709 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq44354 eq77
    | exact resolve eq77 eq44354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq44354
  have eq44903 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq44709
       have i₂ := eq44231
       grind)
    | exact superpose eq44231 eq44709
    | exact resolve eq44709 eq44231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44231 eq44709
  have eq44955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44903 eq15
    | exact resolve eq15 eq44903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44903
  have eq45000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq44955
    | exact resolve eq44955 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44955
  have eq45011 : False := by grind
  exact eq45011

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation575 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 (M.op X3 (M.op X1 X0))) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq24
    | exact resolve eq24 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq72 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq82 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) (M.op (τ X1) (τ X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 X3
       have i₂ := eq20 X2 X0 X1 X3
       grind)
    | (have i₁ := eq9 (M.op X2 X0) X2 X1
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq20 (M.op X1 X2) X1 x X0
       grind)
    | (have i₁ := eq9 X0 X1 X1
       have i₂ := eq20 (M.op X1 X0) X1 X2 X1
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1791 : ∀ X0 X1 : G, (τ (k (k (σ X0) X1) (k (σ X0) X1))) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq72 (k (σ X0) X1)
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq72
    | exact resolve eq72 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq1814 : ∀ X0 X1 : G, (k (τ (k (σ X0) X1)) (k X0 (τ X1))) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1791 X0 X1
       have i₂ := eq35 X0 X1 (k (σ X0) X1)
       grind)
    | exact superpose eq35 eq1791
    | (have j0 := eq1791 X0 X1
       grind)
    | exact resolve eq1791 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1791
  have eq1817 : ∀ X0 X1 : G, (k (k X0 (τ X1)) (k X0 (τ X1))) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1814 X0 X1
       have i₂ := eq30 X0 X1
       grind)
    | exact superpose eq30 eq1814
    | (have j0 := eq1814 X0 X1
       grind)
    | exact resolve eq1814 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1814
  have eq1820 : ∀ X0 X1 : G, (k (k X0 (τ X1)) (k X0 (τ X1))) = (M.op (k X0 (τ X1)) (k X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1817 X0 X1
       have j1 := eq12 (k X0 (τ X1)) (k X0 (τ X1))
       grind)
    | (have r₁ := eq1817 X0 X1
       have r₂ := eq12 X0 (k X0 (τ X1))
       grind)
    | exact resolve eq1817 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq2441 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = X2 ∨ (k (σ X2) X0) = (σ (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq82 X2 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq82 X2 X0
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X1)
       have r₂ := eq82 (M.op (τ X1) (τ X1)) X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2444 : ∀ X0 X1 X2 : G, (k (σ X2) X0) = (σ (M.op X2 (τ X0))) ∨ (τ X0) = X2 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2441 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2441
  have eq5161 : ∀ X0 X1 : G, (k (k X1 X0) (k X1 X0)) = (M.op (k X1 X0) (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1820
    | exact resolve eq1820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5179 : ∀ X0 X1 : G, (M.op (τ (k X0 X1)) (τ (k X0 X1))) = (k (τ (k X0 X1)) (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 (τ X1) X0
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq1820
    | exact resolve eq1820 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq5211 : ∀ X0 X1 : G, (M.op (τ (k X0 X1)) (τ (k X0 X1))) = (τ (k (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5179 X0 X1
       have i₂ := eq33 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq33 eq5179
    | exact resolve eq5179 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179
  have eq5219 : ∀ X0 X1 : G, (M.op (τ (k X0 X1)) (τ (k X0 X1))) = (τ (M.op (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5211 X0 X1
       have i₂ := eq5161 X1 X0
       grind)
    | exact superpose eq5161 eq5211
    | exact resolve eq5211 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5211
  have eq5263 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ (k X0 X1))) = (k (σ (k X0 X1)) (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5161 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5161
    | exact resolve eq5161 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5306 : ∀ X0 X1 : G, (σ (k (k X0 X1) (k X0 X1))) = (M.op (σ (k X0 X1)) (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5263 X0 X1
       have i₂ := eq15 (k X0 X1) (k X0 X1)
       grind)
    | exact superpose eq15 eq5263
    | exact resolve eq5263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq5316 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ (k X0 X1))) = (σ (M.op (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5306 X0 X1
       have i₂ := eq5161 X1 X0
       grind)
    | exact superpose eq5161 eq5306
    | exact resolve eq5306 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161 eq5306
  have eq16430 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2444 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2444
    | exact resolve eq2444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq16501 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16430 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq16430
    | (have j0 := eq16430 X0 X1 X2
       grind)
    | exact resolve eq16430 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16430
  have eq16566 : ∀ X0 X1 X2 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq16501 X1 X0 X2
       grind)
    | exact superpose eq16501 eq10
    | (have j1 := eq16501 (k X0 X1) (τ (σ (M.op X0 X1))) X2
       grind)
    | exact resolve eq10 eq16501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16501
  have eq16636 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X2 X1) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16566 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq16566
    | (have j0 := eq16566 X0 X1 X0
       grind)
    | exact resolve eq16566 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16566
  have eq16786 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq16636 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16636
  have eq16787 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq16786 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16786
  have eq16987 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq16787 X0 (τ X1)
       grind)
    | exact superpose eq16787 eq19
    | (have j1 := eq16787 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq17021 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq16787 (σ X0) (σ X1)
       grind)
    | exact superpose eq16787 eq15
    | (have j1 := eq16787 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq16787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16787
  have eq18471 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16987 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16987
    | exact resolve eq16987 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16987
  have eq18546 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18471 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18471
    | (have j0 := eq18471 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq18471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18471
  have eq19434 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17021 x y
       grind)
    | exact superpose eq17021 eq16
    | (have j1 := eq17021 x y
       grind)
    | exact resolve eq16 eq17021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19440 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X0) (M.op X2 (M.op X2 (σ (k X0 X1))))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq17021 X0 X1
       grind)
    | exact superpose eq17021 eq9
    | (have j1 := eq17021 X0 X1
       grind)
    | exact resolve eq9 eq17021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17021
  have eq19629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq19434
       have i₂ := eq18546 y x
       grind)
    | exact superpose eq18546 eq19434
    | (have j1 := eq18546 (σ x) (σ y)
       grind)
    | (have r₁ := eq19434
       have r₂ := eq18546 y x
       grind)
    | (have r₁ := eq19434
       have r₂ := eq18546 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq19434
       have r₂ := eq18546 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq19434 eq18546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18546 eq19434
  have eq19634 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq19629
  have eq19640 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19634
       grind)
    | exact superpose eq19634 eq16
    | exact resolve eq16 eq19634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19634
  have eq49004 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X0)) (M.op X2 (M.op X2 (σ (τ (k X0 X1)))))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19440 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq19440
    | (have j0 := eq19440 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq19440 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq19440
  have eq49344 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X0)) (M.op X2 (M.op X2 (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49004 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq49004
    | (have j0 := eq49004 X0 X1 X2
       grind)
    | exact resolve eq49004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49004
  have eq49398 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op X0 (M.op X2 (M.op X2 (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49344 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49344
    | (have j0 := eq49344 X0 X1 X2
       grind)
    | exact resolve eq49344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49344
  have eq49432 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (k X0 X1)))) = X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49398 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq49398
    | (have j0 := eq49398 X0 X1 X2
       grind)
    | exact resolve eq49398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49398
  have eq49456 : ∀ X0 X1 X2 : G, (σ (τ X0)) = X1 ∨ (M.op X0 (M.op X2 (M.op X2 (k X0 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49432 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq49432
    | (have j0 := eq49432 X0 X1 X2
       grind)
    | exact resolve eq49432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49432
  have eq49465 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 (k X0 X1)))) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49456 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49456
    | (have j0 := eq49456 X0 X1 X2
       grind)
    | exact resolve eq49456 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49456
  have eq49616 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op X1 (k X1 X0)) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102 X1 x (k X1 X0) X2
       have i₂ := eq49465 X1 X0 x
       grind)
    | exact superpose eq49465 eq102
    | (have j1 := eq49465 (M.op X2 (M.op X2 X0)) (M.op X1 (k X1 X0)) X2
       grind)
    | exact resolve eq102 eq49465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq49465
  have eq50721 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (k X0 (M.op X1 X2)))) = X2 ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X1 X1 X2
       have i₂ := eq49616 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq49616 eq105
    | (have j1 := eq49616 (M.op X1 (M.op X0 (k X0 (M.op X1 X2)))) X2 X2
       grind)
    | exact resolve eq105 eq49616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49616
  have eq51858 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X2 ∨ (M.op X1 (M.op X1 X0)) = (k X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X1 X2 (k X2 (M.op X2 X0))
       have i₂ := eq50721 X2 X2 X0
       grind)
    | exact superpose eq50721 eq105
    | (have j1 := eq50721 X2 X2 X0
       grind)
    | exact resolve eq105 eq50721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50721
  have eq52547 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X2 ∨ (M.op X3 (M.op X3 (M.op X1 (M.op X1 X2)))) = (k X0 (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq105 X0 X1 X2
       have i₂ := eq51858 (M.op X1 (M.op X1 X2)) X3 X0
       grind)
    | exact superpose eq51858 eq105
    | (have j1 := eq51858 (M.op X1 (M.op X1 X2)) X3 X0
       grind)
    | exact resolve eq105 eq51858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51858
  have eq52772 : ∀ X0 X1 X2 : G, (k X0 (M.op X0 (M.op X1 (M.op X1 X2)))) = X2 ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52547 X0 X1 X2 x
       have i₂ := eq105 x X1 X2
       grind)
    | exact superpose eq105 eq52547
    | (have j0 := eq52547 X0 X1 X2 x
       grind)
    | exact resolve eq52547 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq52547
  have eq53818 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5316 X0 (M.op X0 (M.op X1 (M.op X1 x)))
       have i₂ := eq52772 X0 X1 x
       grind)
    | exact superpose eq52772 eq5316
    | (have j1 := eq52772 (σ X0) X1 (σ (M.op X0 X0))
       grind)
    | exact resolve eq5316 eq52772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52772
  have eq56893 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq19640
       have i₂ := eq53818 x X0
       grind)
    | exact superpose eq53818 eq19640
    | (have j1 := eq53818 x X0
       grind)
    | (have r₁ := eq19640
       have r₂ := eq53818 x x
       grind)
    | (have r₁ := eq19640
       have r₂ := eq53818 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq19640 eq53818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56975 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq56893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56893
  have eq57203 : ∀ X0 : G, y = (τ (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq56975 X0
       grind)
    | exact superpose eq56975 eq10
    | (have j1 := eq56975 X0
       grind)
    | exact resolve eq10 eq56975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56975
  have eq57308 : ∀ X0 : G, x = y ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq57203 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq57203
    | (have j0 := eq57203 X0
       grind)
    | exact resolve eq57203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57203
  have eq57311 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq57308 X0
       grind)
    | exact superpose eq57308 eq16
    | (have j1 := eq57308 X0
       grind)
    | exact resolve eq16 eq57308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57308
  have eq57312 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq57311 X0
       have j1 := eq53818 x X0
       grind)
    | (have r₁ := eq57311 X0
       have r₂ := eq53818 x x
       grind)
    | (have r₁ := eq57311 X0
       have r₂ := eq53818 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq57311 eq53818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53818 eq57311
  have eq57880 : x ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19640
       have i₂ := eq57312 (σ x)
       grind)
    | exact superpose eq57312 eq19640
    | exact resolve eq19640 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19640
  have eq57905 : ∀ X0 X1 : G, x = (σ (M.op (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5316 X0 X1
       have i₂ := eq57312 (σ (k X0 X1))
       grind)
    | exact superpose eq57312 eq5316
    | exact resolve eq5316 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5316
  have eq57924 : ∀ X0 X1 : G, x = (τ (M.op (k X0 X1) (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5219 X0 X1
       have i₂ := eq57312 (τ (k X0 X1))
       grind)
    | exact superpose eq57312 eq5219
    | exact resolve eq5219 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5219
  have eq57931 : x = (τ x) := by
    first
    | (have i₁ := eq57924 x x
       have i₂ := eq57312 (k x x)
       grind)
    | exact superpose eq57312 eq57924
    | exact resolve eq57924 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57924
  have eq57933 : x = (σ x) := by
    first
    | (have i₁ := eq57905 x x
       have i₂ := eq57312 (k x x)
       grind)
    | exact superpose eq57312 eq57905
    | exact resolve eq57905 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57905
  have eq57935 : x ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57880
       have i₂ := eq57312 x
       grind)
    | exact superpose eq57312 eq57880
    | exact resolve eq57880 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57880
  have eq58094 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq57935
       have r₂ := eq57933
       grind)
    | exact resolve eq57935 eq57933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57935
  have eq58193 : x = (σ y) := by
    first
    | (have i₁ := eq58094
       have i₂ := eq57933
       grind)
    | exact superpose eq57933 eq58094
    | exact resolve eq58094 eq57933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58094
  have eq59832 : y = (τ x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq58193
       grind)
    | exact superpose eq58193 eq10
    | exact resolve eq10 eq58193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58193
  have eq59948 : x = y := by
    first
    | (have i₁ := eq59832
       have i₂ := eq57931
       grind)
    | exact superpose eq57931 eq59832
    | exact resolve eq59832 eq57931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57931 eq59832
  have eq60629 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59948
       grind)
    | exact superpose eq59948 eq16
    | exact resolve eq16 eq59948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59948
  have eq60631 : x ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq60629
       have i₂ := eq57312 (σ x)
       grind)
    | exact superpose eq57312 eq60629
    | exact resolve eq60629 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60629
  have eq60632 : x ≠ (σ x) := by
    first
    | (have i₁ := eq60631
       have i₂ := eq57312 x
       grind)
    | exact superpose eq57312 eq60631
    | exact resolve eq60631 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57312 eq60631
  have eq60633 : False := by grind
  exact eq60633
