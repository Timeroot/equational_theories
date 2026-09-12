import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1833`: `x = (x ◇ (x ◇ x)) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation1833 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1833 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1833.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
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
  have eq568 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 y x
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
  have eq575 : (k x x) ≠ (k y y) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq568
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq568
    | exact resolve eq568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1230 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 x y
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
  have eq1240 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1230
    | exact resolve eq1230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1250 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1240
       have i₂ := eq21 (σ x) (σ y)
       grind)
    | exact superpose eq21 eq1240
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1240
       have r₂ := eq21 (σ x) (σ y)
       grind)
    | (have r₁ := eq1240
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1240
       have r₂ := eq21 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1240 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1240
  have eq1252 : x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1250
  have eq1328 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1252
       grind)
    | exact superpose eq1252 eq9
    | exact resolve eq9 eq1252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252
  have eq1329 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1328
  have eq1330 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1329
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1329
    | exact resolve eq1329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1331 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1330
  have eq1332 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1331
  have eq1410 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1332
       grind)
    | exact superpose eq1332 eq10
    | exact resolve eq10 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1412 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1410
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1410
    | exact resolve eq1410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1413 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1412
  have eq1417 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1413
       grind)
    | exact superpose eq1413 eq22
    | exact resolve eq22 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : (k x x) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1417
    | exact resolve eq1417 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1417
  have eq1486 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq575
       have i₂ := eq1464
       grind)
    | exact superpose eq1464 eq575
    | (have r₁ := eq575
       have r₂ := eq1464
       grind)
    | exact resolve eq575 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq1464
  have eq1489 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1486
  have eq1493 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1489
       have i₂ := eq20 (σ y) (σ x)
       grind)
    | exact superpose eq20 eq1489
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1489
       have r₂ := eq20 (σ y) (σ x)
       grind)
    | (have r₁ := eq1489
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1489
       have r₂ := eq20 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1489 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1489
  have eq1494 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1493
  have eq1495 : x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1494
  have eq1497 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1495
       have r₂ := eq1413
       grind)
    | exact resolve eq1495 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq1495
  have eq1498 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1497
       grind)
    | exact superpose eq1497 eq9
    | exact resolve eq9 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1499 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1498
  have eq1500 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1499
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1499
    | exact resolve eq1499 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499
  have eq1501 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1500
  have eq1502 : (σ x) = (σ y) := by grind
  clear eq1501
  have eq1504 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1502
       grind)
    | exact superpose eq1502 eq15
    | exact resolve eq15 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq1551 : x = y := by
    first
    | (have i₁ := eq1504
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1504
    | exact resolve eq1504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1554 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1551
       grind)
    | exact superpose eq1551 eq9
    | exact resolve eq9 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1555 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1554
  have eq1556 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1555
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1555
    | exact resolve eq1555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq1557 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1556
  have eq1558 : False := by grind
  exact eq1558

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_y_pxy_x_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq188 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  have eq420 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq419
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq419
    | exact resolve eq419 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq422 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq420
    | exact resolve eq420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq422 eq187
    | exact resolve eq187 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq422
  have eq518 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq511
       have r₂ := eq27
       grind)
    | exact resolve eq511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq628 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq518 eq13
    | exact resolve eq13 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq632 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq628
  have eq636 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq633
       have i₂ := eq632 y
       grind)
    | exact superpose eq632 eq633
    | exact resolve eq633 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq669 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq636 eq153
    | exact resolve eq153 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq636
  have eq673 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq669
    | exact resolve eq669 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq669
  have eq674 : y = (k y y) := by grind
  clear eq673
  have eq680 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq41
    | exact resolve eq41 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq684 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq680
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq680
    | exact resolve eq680 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq680
  have eq1411 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq16
    | exact resolve eq16 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1412 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq175
    | exact resolve eq175 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq176
    | exact resolve eq176 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq198
    | exact resolve eq198 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1425 : ∀ X0 X1 : G, (M.op (M.op X0 (k X0 X0)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq16
    | exact resolve eq16 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1438 : ∀ X0 X1 : G, (M.op (M.op X0 (k X0 X0)) (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1425 X0 X1
       have i₂ := eq632 X1
       grind)
    | exact superpose eq632 eq1425
    | exact resolve eq1425 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1466 : x = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq1412 y
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq1412
    | exact resolve eq1412 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1513 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1516 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op X0 X0)) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq1466 eq178
    | exact resolve eq178 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1466
  have eq1643 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq1516
    | exact resolve eq1516 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1646 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq1513
    | exact resolve eq1513 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq1807 : x ≠ (M.op x x) ∨ x = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq1643 eq13
    | exact resolve eq13 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1809 : x = (k (M.op x (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1643 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643
  have eq1817 : x = (k (M.op x (M.op x y)) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1809
       have i₂ := eq632 x
       grind)
    | exact superpose eq632 eq1809
    | exact resolve eq1809 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1818 : x ≠ (k x x) ∨ x = (k (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1807
       have i₂ := eq632 x
       grind)
    | exact superpose eq632 eq1807
    | exact resolve eq1807 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1822 : x = (k (M.op x (M.op x y)) x) := by
    first
    | (have r₁ := eq1818
       have r₂ := eq1817
       grind)
    | exact resolve eq1818 eq1817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817 eq1818
  have eq1824 : (σ x) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | exact superpose eq1822 eq40
    | exact resolve eq40 eq1822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1822
  have eq1827 : (σ x) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq1824
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1824
    | exact resolve eq1824 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1833 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1827 eq182
    | (have j0 := eq182 X0 (σ x) x
       grind)
    | exact resolve eq182 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1836 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1833 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq1833
    | exact resolve eq1833 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1841 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1836 X0
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq1836
    | (have j0 := eq1836 X0
       grind)
    | exact resolve eq1836 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq1981 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1841 X0
       have i₂ := eq28 (σ (M.op x sF0)) sF2
       grind)
    | exact superpose eq28 eq1841
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq1841 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1983 : (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1841 y
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq1841
    | exact resolve eq1841 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq2006 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1981 X0
       have j1 := eq188 (σ x)
       grind)
    | (have r₁ := eq1981 X0
       have r₂ := eq188 (σ x)
       grind)
    | exact resolve eq1981 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1981
  have eq2012 : ∀ X0 : G, (M.op (σ x) (k X0 X0)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1827 eq2006
    | exact resolve eq2006 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2016 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1415 eq2012
    | exact resolve eq2012 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415 eq2012
  have eq2018 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2016
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq2016
    | exact resolve eq2016 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq2117 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2018 eq1983
    | exact resolve eq1983 eq2018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq2118 : (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1983
       have i₂ := eq28 (σ (M.op x sF0)) sF2
       grind)
    | exact superpose eq28 eq1983
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq1983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1983
  have eq2127 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq2117
  have eq2136 : (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq188 (σ x)
       grind)
    | (have r₁ := eq2118
       have r₂ := eq188 (σ x)
       grind)
    | exact resolve eq2118 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq2118
  have eq2137 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1646 eq2127
    | exact resolve eq2127 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2143 : (σ (M.op x (M.op x y))) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1827 eq2136
    | exact resolve eq2136 eq1827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827 eq2136
  have eq2148 : (σ (M.op x (M.op x y))) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2143
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq2143
    | exact resolve eq2143 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143
  have eq2155 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) y) (M.op X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq2137 eq176
    | exact resolve eq176 eq2137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2137
  have eq2174 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) y) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2155 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq2155
    | exact resolve eq2155 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155
  have eq2233 : (σ x) = (M.op (M.op (σ x) y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq684 eq2174
    | exact resolve eq2174 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq4596 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq684 eq1413
    | exact resolve eq1413 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq5487 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1411 y X0 X1
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq1411
    | exact resolve eq1411 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5488 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq684 eq1411
    | exact resolve eq1411 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq1411
  have eq5611 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1438 X0 y
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq1438
    | exact resolve eq1438 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674 eq1438
  have eq6269 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq175 eq5487
    | exact resolve eq5487 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq6270 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | exact superpose eq176 eq5487
    | exact resolve eq5487 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq5487
  have eq6308 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq6269
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6269
    | exact resolve eq6269 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6269
  have eq6440 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6308 eq2148
    | exact resolve eq2148 eq6308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148 eq6308
  have eq6457 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq6440
    | exact resolve eq6440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6440
  have eq6637 : (σ x) = (M.op (M.op (σ x) y) (σ x)) := by
    first
    | exact superpose eq6270 eq1646
    | exact resolve eq1646 eq6270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq6643 : (σ x) = (M.op (M.op (σ x) y) (σ y)) := by
    first
    | exact superpose eq6270 eq4596
    | exact resolve eq4596 eq6270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596 eq6270
  have eq8211 : (M.op (σ x) y) = (M.op (M.op (M.op (σ x) y) (σ x)) (σ y)) := by
    first
    | exact superpose eq6643 eq5488
    | exact resolve eq5488 eq6643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643
  have eq8212 : (M.op (σ x) y) = (M.op (M.op (M.op (σ x) y) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2233 eq5488
    | exact resolve eq5488 eq2233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2233 eq5488
  have eq8358 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6637 eq8212
    | exact resolve eq8212 eq6637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq8359 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq6637 eq8211
    | exact resolve eq8211 eq6637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6637 eq8211
  have eq8427 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq8358
    | exact resolve eq8358 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358
  have eq8428 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq26 eq8359
    | exact resolve eq8359 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8359
  have eq8461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6457 eq8427
    | exact resolve eq8427 eq6457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6457 eq8427
  have eq8468 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq8461
       have r₂ := eq27
       grind)
    | exact resolve eq8461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8701 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq8468 eq142
    | exact resolve eq142 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq8737 : (σ x) = (M.op (M.op (σ x) (σ x)) y) := by
    first
    | exact superpose eq8468 eq5611
    | exact resolve eq5611 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8751 : (σ x) = (M.op (k (σ x) (σ x)) y) := by
    first
    | (have i₁ := eq8737
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq8737
    | exact resolve eq8737 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8737
  have eq8767 : x = (k x x) := by
    first
    | exact superpose eq30 eq8701
    | exact resolve eq8701 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8701
  have eq8772 : (σ x) = (M.op (σ x) y) := by
    first
    | exact superpose eq8468 eq8751
    | exact resolve eq8751 eq8468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8468 eq8751
  have eq9023 : x = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq5611 x
       have i₂ := eq8767
       grind)
    | exact superpose eq8767 eq5611
    | exact resolve eq5611 eq8767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5611
  have eq9042 : x = (M.op (k x x) y) := by
    first
    | (have i₁ := eq9023
       have i₂ := eq632 x
       grind)
    | exact superpose eq632 eq9023
    | exact resolve eq9023 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq9023
  have eq9080 : x = (M.op x y) := by
    first
    | (have i₁ := eq9042
       have i₂ := eq8767
       grind)
    | exact superpose eq8767 eq9042
    | exact resolve eq9042 eq8767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8767 eq9042
  have eq9095 : x = (M.op x y) := by
    first
    | (have i₁ := eq9080
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9080
    | exact resolve eq9080 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9080
  have eq9105 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9095
       grind)
    | exact superpose eq9095 eq22
    | exact resolve eq22 eq9095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9095
  have eq9190 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9105 eq20
    | exact resolve eq20 eq9105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9105
  have eq9269 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8772 eq8428
    | exact resolve eq8428 eq8772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8428 eq8772
  have eq9341 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9269 eq27
    | exact resolve eq27 eq9269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9269
  have eq9397 : False := by grind
  exact eq9397

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74
    | exact resolve eq74 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq79
    | exact resolve eq79 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq106 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq93
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq108
  have eq129 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62
    | (have j0 := eq62 y x
       grind)
    | exact resolve eq62 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq62
    | (have j0 := eq62 (σ y) (σ x)
       grind)
    | exact resolve eq62 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : y ≠ (M.op y y) ∨ (M.op x y) = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq274 eq13
    | (have j0 := eq13 y y
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq446 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X0 X0) X0 X1 X2
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 y x X0 X1
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq58
    | (have j0 := eq58 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq58 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X2 (M.op X0 X1) X1
       have i₂ := eq62 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq62 eq58
    | exact resolve eq58 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq603 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq14
    | (have j1 := eq69 X0 X0
       grind)
    | exact resolve eq14 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq613 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq607 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq614 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq603 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq620 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq613 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq613 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq613 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq626 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq702 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq63 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq63
    | (have j0 := eq63 X0
       grind)
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2006 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq221 X0 sF4
       have i₂ := eq62 sF4 sF4
       grind)
    | exact superpose eq62 eq221
    | exact resolve eq221 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2976 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq459
    | exact resolve eq459 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3003 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2976 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2976
    | (have j0 := eq2976 y x
       grind)
    | exact resolve eq2976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3005 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq2976
    | (have j0 := eq2976 (σ y) (σ x)
       grind)
    | exact resolve eq2976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3182 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq464 x X1 X0
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq464
    | exact resolve eq464 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq3225 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq466 sF2 X1 x
       have i₂ := eq62 sF2 sF2
       grind)
    | exact superpose eq62 eq466
    | exact resolve eq466 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq3261 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3182 sF0 sF0
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq3182
    | exact resolve eq3182 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182
  have eq3428 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq455 (M.op y X0) X0
       have i₂ := eq62 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq62 eq455
    | exact resolve eq455 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq3452 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq457 (M.op sF3 x) x
       have i₂ := eq62 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq62 eq457
    | exact resolve eq457 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq3470 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3225 sF4 sF4
       have i₂ := eq59 sF4
       grind)
    | exact superpose eq59 eq3225
    | exact resolve eq3225 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3569 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq59 (M.op X0 X1)
       grind)
    | exact superpose eq59 eq462
    | exact resolve eq462 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq5306 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X1 (M.op (σ (τ X0)) X2)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq614 (τ X0) X1 X2
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq614
    | (have j0 := eq614 (τ X0) X1 X2
       grind)
    | exact resolve eq614 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq614
  have eq5327 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5306 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5306
    | (have j0 := eq5306 X0 X1 X2
       grind)
    | exact resolve eq5306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5306
  have eq5338 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5327 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5327
    | (have j0 := eq5327 X0 X1 X2
       grind)
    | exact resolve eq5327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327
  have eq7014 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 X1 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq446
    | exact resolve eq446 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7057 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq62 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq62 eq446
    | exact resolve eq446 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq11980 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11980
    | exact resolve eq11980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11980
  have eq11998 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq11987
       have r₂ := eq27
       grind)
    | exact resolve eq11987 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11987
  have eq12000 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq11998
    | exact resolve eq11998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11998
  have eq12006 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12000 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq12000
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq12000
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12000
       grind)
    | exact resolve eq12 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12007 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12000 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12000
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12000
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12000
       grind)
    | exact resolve eq13 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12000
  have eq12020 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12007
  have eq12021 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12006
  have eq12022 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq12021
    | exact resolve eq12021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12021
  have eq12023 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12022
  have eq12025 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12020 eq106
    | exact resolve eq106 eq12020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq12020
  have eq12044 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq12025
    | exact resolve eq12025 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12025
  have eq12045 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq12044
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq12044
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq12044
       have r₂ := eq13 y x
       grind)
    | exact resolve eq12044 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12044
  have eq12157 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq12045
       grind)
    | exact superpose eq12045 eq92
    | exact resolve eq92 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq12164 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12045
       grind)
    | exact superpose eq12045 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12045
  have eq12173 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12164
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12164
    | exact resolve eq12164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12164
  have eq12174 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12173
  have eq12181 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12157
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12157
    | exact resolve eq12157 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12157
  have eq12214 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12181 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq12181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12214
    | exact resolve eq12214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12214
  have eq12221 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12220
  have eq13319 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2976 x y
       have i₂ := eq12174
       grind)
    | exact superpose eq12174 eq2976
    | exact resolve eq2976 eq12174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13320 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq13452 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12221 eq2976
    | exact resolve eq2976 eq12221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12221
  have eq18776 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12023 eq81
    | exact resolve eq81 eq12023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12023
  have eq18790 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18776
  have eq18815 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18790 eq62
    | exact resolve eq62 eq18790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18790
  have eq20472 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13319
       have i₂ := eq12174
       grind)
    | exact superpose eq12174 eq13319
    | exact resolve eq13319 eq12174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20478 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq13319
       grind)
    | exact superpose eq13319 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13319
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13319
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13319
       grind)
    | exact resolve eq12 eq13319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20493 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13319
  have eq20495 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq20472
  have eq20497 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq20478
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq20478
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq20478
       have r₂ := eq12 x y
       grind)
    | exact resolve eq20478 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20478
  have eq20498 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20495
       have r₂ := eq13320
       grind)
    | exact resolve eq20495 eq13320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20495
  have eq20499 : y = (M.op x y) ∨ x ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20497
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20497
    | exact resolve eq20497 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20497
  have eq20500 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20499
  have eq20536 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq20498
       grind)
    | exact superpose eq20498 eq56
    | exact resolve eq56 eq20498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq20562 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq62 x x
       have i₂ := eq20498
       grind)
    | exact superpose eq20498 eq62
    | exact resolve eq62 eq20498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20498
  have eq20605 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq20562
       grind)
    | exact superpose eq20562 eq114
    | exact resolve eq114 eq20562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20562
  have eq20643 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20605
       have r₂ := eq13320
       grind)
    | exact resolve eq20605 eq13320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20605
  have eq20644 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq20643
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20643
    | exact resolve eq20643 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20643
  have eq21917 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13452
  have eq22701 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7014 x y
       have i₂ := eq12174
       grind)
    | exact superpose eq12174 eq7014
    | exact resolve eq7014 eq12174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7014 eq12174
  have eq23078 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20536 eq2976
    | exact resolve eq2976 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20536
  have eq23083 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23078
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23078
    | exact resolve eq23078 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23078
  have eq23085 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq23083
       grind)
    | exact superpose eq23083 eq114
    | exact resolve eq114 eq23083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23092 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq22701
       have i₂ := eq23083
       grind)
    | exact superpose eq23083 eq22701
    | exact resolve eq22701 eq23083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22701 eq23083
  have eq23125 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23092
  have eq23127 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq23085
  have eq23133 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq23127
    | exact resolve eq23127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23127
  have eq23273 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq23133 eq20644
    | exact resolve eq20644 eq23133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20644 eq23133
  have eq23291 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq23273
  have eq23484 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18815 eq702
    | exact resolve eq702 eq18815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq18815
  have eq23495 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq23484
       have r₂ := eq23291
       grind)
    | exact resolve eq23484 eq23291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23291 eq23484
  have eq23524 : (τ (σ x)) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23495 eq67
    | exact resolve eq67 eq23495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23495
  have eq23543 : x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq23524
    | exact resolve eq23524 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23524
  have eq42012 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq3261 eq75
    | exact resolve eq75 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq99018 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23125 eq42012
    | exact resolve eq42012 eq23125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23125 eq42012
  have eq99089 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq99018
  have eq99094 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq99089
       have r₂ := eq20493
       grind)
    | exact resolve eq99089 eq20493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20493 eq99089
  have eq99095 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99094
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99094
    | exact resolve eq99094 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99094
  have eq99101 : (τ (σ y)) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99095 eq67
    | exact resolve eq67 eq99095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq99095
  have eq99145 : y = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq99101
    | exact resolve eq99101 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99101
  have eq99331 : x = y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99145 eq23543
    | exact resolve eq23543 eq99145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23543 eq99145
  have eq99353 : x = y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq99331
  have eq99362 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq99353
       have r₂ := eq13320
       grind)
    | exact resolve eq99353 eq13320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13320 eq99353
  have eq99438 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq99362
       grind)
    | exact superpose eq99362 eq14
    | exact resolve eq14 eq99362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99455 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3569 x x y
       have i₂ := eq99362
       grind)
    | exact superpose eq99362 eq3569
    | exact resolve eq3569 eq99362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100302 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99438 y
       have i₂ := eq99362
       grind)
    | exact superpose eq99362 eq99438
    | exact resolve eq99438 eq99362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99438
  have eq100358 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq100302
  have eq100431 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq483 x (M.op y y) x
       have i₂ := eq100358
       grind)
    | exact superpose eq100358 eq483
    | exact resolve eq483 eq100358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq100607 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3569 x X0 x
       have i₂ := eq99455 x
       grind)
    | exact superpose eq99455 eq3569
    | exact resolve eq3569 eq99455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99455
  have eq103312 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100607 (M.op y y)
       have i₂ := eq100358
       grind)
    | exact superpose eq100358 eq100607
    | exact resolve eq100607 eq100358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100358 eq100607
  have eq103426 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq103312
  have eq103446 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99362
       have i₂ := eq103426
       grind)
    | exact superpose eq103426 eq99362
    | exact resolve eq99362 eq103426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103426
  have eq103522 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq103446
  have eq104183 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20500
       have i₂ := eq103522
       grind)
    | exact superpose eq103522 eq20500
    | (have r₁ := eq20500
       have r₂ := eq103522
       grind)
    | exact resolve eq20500 eq103522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20500
  have eq104248 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq103522
       grind)
    | exact superpose eq103522 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq103522
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq103522
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq103522
       grind)
    | exact resolve eq13 eq103522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103522
  have eq104272 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq104248
  have eq104326 : x ≠ x ∨ y = (M.op x y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq104183
  have eq104327 : y = (M.op x y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq104326
  have eq104353 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq104327
       have r₂ := eq50
       grind)
    | exact resolve eq104327 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq104327
  have eq104363 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq104353
       grind)
    | exact superpose eq104353 eq44
    | exact resolve eq44 eq104353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104353
  have eq104415 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104363
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq104363
    | exact resolve eq104363 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104363
  have eq104421 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq104415
       have r₂ := eq51
       grind)
    | exact resolve eq104415 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq104415
  have eq104440 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81 eq104421
    | exact resolve eq104421 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq104448 : (τ (σ x)) = (k x y) := by
    first
    | exact superpose eq104421 eq55
    | exact resolve eq55 eq104421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq104470 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104421 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104476 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq104470
    | exact resolve eq104470 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104470
  have eq104484 : x = (k x y) := by
    first
    | exact superpose eq28 eq104448
    | exact resolve eq104448 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104448
  have eq104488 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq104476
    | exact resolve eq104476 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104476
  have eq106153 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq626 x x
       have i₂ := eq104272
       grind)
    | exact superpose eq104272 eq626
    | (have j0 := eq626 x x
       grind)
    | exact resolve eq626 eq104272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104272
  have eq106154 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq106153
  have eq106155 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq106154
  have eq106176 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106155
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq106155
    | exact resolve eq106155 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106155
  have eq107658 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106176 eq21917
    | (have r₁ := eq21917
       have r₂ := eq106176
       grind)
    | exact resolve eq21917 eq106176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21917 eq106176
  have eq107762 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq107658
  have eq107763 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq107762
  have eq107927 : x ≠ x ∨ y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq104440
       grind)
    | exact superpose eq104440 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq104440
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq104440
       grind)
    | exact resolve eq12 eq104440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107929 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq104440
       grind)
    | exact superpose eq104440 eq14
    | exact resolve eq14 eq104440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104440
  have eq107953 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq107927
  have eq107982 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107953
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107953
    | exact resolve eq107953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107953
  have eq107983 : y = (M.op x y) ∨ (k x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq107982
  have eq107987 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107983
       have i₂ := eq104484
       grind)
    | exact superpose eq104484 eq107983
    | exact resolve eq107983 eq104484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104484 eq107983
  have eq109578 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq104488 eq14
    | exact resolve eq14 eq104488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104488
  have eq110342 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq107763 eq14
    | exact resolve eq14 eq107763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107763
  have eq111228 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq107987
       grind)
    | exact superpose eq107987 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq107987
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq107987
       grind)
    | exact resolve eq13 eq107987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107987
  have eq111252 : x = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq111228
  have eq112372 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq626 x x
       have i₂ := eq111252
       grind)
    | exact superpose eq111252 eq626
    | (have j0 := eq626 x x
       grind)
    | exact resolve eq626 eq111252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111252
  have eq112373 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq112372
  have eq112374 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq112373
  have eq112395 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq112374
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq112374
    | exact resolve eq112374 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112374
  have eq114844 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq112395 eq2006
    | exact resolve eq2006 eq112395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006 eq112395
  have eq143307 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq100431 y
       have i₂ := eq99362
       grind)
    | exact superpose eq99362 eq100431
    | exact resolve eq100431 eq99362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99362 eq100431
  have eq143401 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq143307
  have eq143437 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq143401
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq143401
    | exact resolve eq143401 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143401
  have eq143459 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq143437
       grind)
    | exact superpose eq143437 eq114
    | exact resolve eq114 eq143437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143437
  have eq143583 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq143459
  have eq143599 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq143583
    | exact resolve eq143583 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143583
  have eq187029 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq7057 x (M.op y y)
       have i₂ := eq107929 x
       grind)
    | exact superpose eq107929 eq7057
    | exact resolve eq7057 eq107929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107929
  have eq187146 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq187029
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq187029
    | exact resolve eq187029 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187029
  have eq187150 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq187146
       grind)
    | exact superpose eq187146 eq114
    | exact resolve eq114 eq187146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq187146
  have eq187324 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq187150
  have eq187347 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq187324
    | exact resolve eq187324 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187324
  have eq193876 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq109578 eq7057
    | exact resolve eq7057 eq109578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109578
  have eq193974 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq193876
    | exact resolve eq193876 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193876
  have eq206774 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq110342 eq7057
    | exact resolve eq7057 eq110342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110342
  have eq206884 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq206774
    | exact resolve eq206774 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206774
  have eq207728 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq206884 eq275
    | exact resolve eq275 eq206884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq207798 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206884 eq3569
    | (have j0 := eq3569 (σ y) X0 (σ x)
       grind)
    | exact resolve eq3569 eq206884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq207800 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206884 eq5338
    | exact resolve eq5338 eq206884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5338 eq206884
  have eq207811 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq207800 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207800
  have eq261083 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq207728 eq207798
    | exact resolve eq207798 eq207728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207798
  have eq261169 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq261083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261083
  have eq261882 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq143599 eq207811
    | exact resolve eq207811 eq143599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143599 eq207811
  have eq261937 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq261882 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261882
  have eq262023 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq207728 eq261937
    | exact resolve eq261937 eq207728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207728
  have eq262037 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq261937 eq62
    | exact resolve eq62 eq261937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262050 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq261937 eq2976
    | exact resolve eq2976 eq261937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976 eq261937
  have eq262074 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq262023
  have eq262251 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq262037 eq261169
    | exact resolve eq261169 eq262037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261169 eq262037
  have eq262312 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq262251
  have eq262405 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq262050 eq262074
    | exact resolve eq262074 eq262050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262050 eq262074
  have eq262465 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq262405
  have eq262485 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq262465 eq59
    | exact resolve eq59 eq262465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq262465
  have eq263275 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq262485 eq262312
    | exact resolve eq262312 eq262485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262312 eq262485
  have eq263358 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq263275
  have eq263361 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq263358
       have r₂ := eq27
       grind)
    | exact resolve eq263358 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263358
  have eq263363 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263361 eq27
    | exact resolve eq27 eq263361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263383 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263361 eq3470
    | exact resolve eq3470 eq263361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3470
  have eq263412 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263361 eq114844
    | exact resolve eq114844 eq263361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114844
  have eq263433 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq263412
  have eq263461 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq263433
    | exact resolve eq263433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263433
  have eq263491 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263383 eq3452
    | exact resolve eq3452 eq263383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452 eq263383
  have eq263610 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263491
       have i₂ := eq62 sF2 sF2
       grind)
    | exact superpose eq62 eq263491
    | exact resolve eq263491 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263491
  have eq263778 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq263610 eq14
    | exact resolve eq14 eq263610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263610
  have eq264378 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq263461 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq263461
       grind)
    | exact resolve eq13 eq263461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263461
  have eq264440 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq264378
       have r₂ := eq263361
       grind)
    | exact resolve eq264378 eq263361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264378
  have eq267467 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq264440 eq187347
    | exact resolve eq187347 eq264440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187347 eq264440
  have eq267508 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq267467
  have eq267537 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq267508
       have r₂ := eq263363
       grind)
    | exact resolve eq267508 eq263363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263363 eq267508
  have eq268352 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq267537 eq28
    | exact resolve eq28 eq267537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq267537
  have eq269126 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq268352
    | exact resolve eq268352 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq268352
  have eq269137 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269126 eq20
    | exact resolve eq20 eq269126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269301 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269126 eq3261
    | exact resolve eq3261 eq269126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq269347 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq269500 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq269137
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq269137
    | exact resolve eq269137 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269137
  have eq270594 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq269500 eq193974
    | exact resolve eq193974 eq269500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193974
  have eq270801 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq270594
       have r₂ := eq27
       grind)
    | exact resolve eq270594 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270594
  have eq273980 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3428 x
       have i₂ := eq269301
       grind)
    | exact superpose eq269301 eq3428
    | exact resolve eq3428 eq269301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq269301
  have eq274104 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq273980
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq273980
    | exact resolve eq273980 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq273980
  have eq280831 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq274104 eq14
    | exact resolve eq14 eq274104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274104
  have eq293730 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263778 eq7057
    | exact resolve eq7057 eq263778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263778
  have eq293866 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263361 eq293730
    | exact resolve eq293730 eq263361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293730
  have eq294069 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq293866
  have eq294073 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq294069
    | exact resolve eq294069 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294069
  have eq294155 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq294073 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq294073
       grind)
    | exact resolve eq13 eq294073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294073
  have eq294224 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq294155
       have r₂ := eq263361
       grind)
    | exact resolve eq294155 eq263361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263361 eq294155
  have eq294954 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq294224 eq113
    | exact resolve eq113 eq294224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq294224
  have eq295070 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq294954
    | exact resolve eq294954 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq294954
  have eq297556 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq295070
       grind)
    | exact superpose eq295070 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq295070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297571 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq297556
  have eq422097 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq280831 eq7057
    | exact resolve eq7057 eq280831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057 eq280831
  have eq422797 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq269126 eq422097
    | exact resolve eq422097 eq269126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422097
  have eq422997 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq422797
       have r₂ := eq269347
       grind)
    | exact resolve eq422797 eq269347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269347 eq422797
  have eq423001 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq422997
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq422997
    | exact resolve eq422997 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422997
  have eq423006 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq288
       have i₂ := eq423001
       grind)
    | exact superpose eq423001 eq288
    | exact resolve eq288 eq423001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq423114 : y ≠ (M.op x y) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq423001
       grind)
    | exact superpose eq423001 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq423001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423001
  have eq423196 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq423114
       have r₂ := eq295070
       grind)
    | exact resolve eq423114 eq295070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295070 eq423114
  have eq423207 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq423006
       have r₂ := eq269126
       grind)
    | exact resolve eq423006 eq269126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269126 eq423006
  have eq423874 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq626 y y
       have i₂ := eq423196
       grind)
    | exact superpose eq423196 eq626
    | (have j0 := eq626 y y
       grind)
    | exact resolve eq626 eq423196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423196
  have eq423880 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq423874
  have eq423881 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq423880
  have eq423924 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq423881
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq423881
    | exact resolve eq423881 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423881
  have eq424483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq423207 eq626
    | (have j0 := eq626 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq626 eq423207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq423207
  have eq424489 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq424483
  have eq424490 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq424489
  have eq424547 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq424490
    | exact resolve eq424490 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424490
  have eq437320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq424547 eq270801
    | exact resolve eq270801 eq424547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270801 eq424547
  have eq437417 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq437320
  have eq437429 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq437417
       have r₂ := eq27
       grind)
    | exact resolve eq437417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437417
  have eq438313 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq437429 eq3005
    | exact resolve eq3005 eq437429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005 eq437429
  have eq438579 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq438313
    | exact resolve eq438313 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438313
  have eq453330 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq438579 eq423924
    | exact resolve eq423924 eq438579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423924 eq438579
  have eq453464 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq453330
  have eq453476 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq453464 eq27
    | exact resolve eq27 eq453464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453464
  have eq453712 : x = (M.op x y) := by
    first
    | (have r₁ := eq453476
       have r₂ := eq269500
       grind)
    | exact resolve eq453476 eq269500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269500 eq453476
  have eq454249 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq453712 eq20
    | exact resolve eq20 eq453712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq454266 : (σ (k x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq453712 eq129
    | exact resolve eq129 eq453712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq454414 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq453712 eq3003
    | exact resolve eq3003 eq453712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq454667 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq454414
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq454414
    | exact resolve eq454414 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq454414
  have eq454797 : (k (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq454266
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq454266
    | exact resolve eq454266 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq454266
  have eq454811 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq454249
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq454249
    | exact resolve eq454249 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454249
  have eq454814 : x = (M.op y y) := by
    first
    | exact superpose eq453712 eq454667
    | exact resolve eq454667 eq453712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454667
  have eq454828 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq104421 eq454797
    | exact resolve eq454797 eq104421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104421 eq454797
  have eq454833 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq454811 eq26
    | exact resolve eq26 eq454811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq455593 : x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq297571
       have i₂ := eq454814
       grind)
    | exact superpose eq454814 eq297571
    | exact resolve eq297571 eq454814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297571 eq454814
  have eq455751 : x = y ∨ x = y := by
    first
    | exact superpose eq453712 eq455593
    | exact resolve eq455593 eq453712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453712 eq455593
  have eq455752 : x = y := by grind
  clear eq455751
  have eq455787 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq455752
       grind)
    | exact superpose eq455752 eq24
    | exact resolve eq24 eq455752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq455752
  have eq456620 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq455787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq455787
    | exact resolve eq455787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq455787
  have eq456771 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq454811 eq456620
    | exact resolve eq456620 eq454811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456620
  have eq458160 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq456771 eq454828
    | exact resolve eq454828 eq456771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454828
  have eq458161 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq454811 eq458160
    | exact resolve eq458160 eq454811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454811 eq458160
  have eq458223 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq458161 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq458161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458161
  have eq458246 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq458223
  have eq458295 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq456771 eq454833
    | exact resolve eq454833 eq456771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454833 eq456771
  have eq466897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq458246 eq458295
    | exact resolve eq458295 eq458246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458246 eq458295
  have eq466898 : False := by grind
  exact eq466898

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_x_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 (M.op x y) X0
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (M.op x y)) (M.op (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq82 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq82
    | exact resolve eq82 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq84
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq84
    | exact resolve eq84 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq127 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq145 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq147
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq147
    | exact resolve eq147 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq170 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq145
    | exact resolve eq145 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq182 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq168
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq168
    | exact resolve eq168 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq184 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq170
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq170
    | exact resolve eq170 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq266 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq266
    | exact resolve eq266 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq286 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (k (M.op X1 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq83 (M.op X1 sF2)
       grind)
    | exact superpose eq83 eq286
    | exact resolve eq286 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq340 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq66
    | exact resolve eq66 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq341 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (M.op (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq63 sF2
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq63
    | exact resolve eq63 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (k (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq346
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq346
    | exact resolve eq346 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq349 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq345
    | exact resolve eq345 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq350 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X1 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq342
    | (have j0 := eq342 X0 X1
       grind)
    | (have r₁ := eq342 X0 X0
       have r₂ := eq83 X0
       grind)
    | exact resolve eq342 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq351 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq341
    | (have j0 := eq341 X0 X1
       grind)
    | (have r₁ := eq341 X0 X0
       have r₂ := eq83 X0
       grind)
    | exact resolve eq341 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq372 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq348 eq9
    | exact resolve eq9 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq373 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq372 X0
       have i₂ := eq83 (k sF2 sF2)
       grind)
    | exact superpose eq83 eq372
    | exact resolve eq372 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq383 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65 sF6
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq396 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq383
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq383
    | exact resolve eq383 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq572 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq182 eq33
    | exact resolve eq33 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq574 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq578 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (k (τ (σ x)) (τ (σ x))) (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq287 (τ sF4) x
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq287
    | exact resolve eq287 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 X2 : G, (M.op X2 (τ (σ x))) = (M.op (M.op X1 (M.op X0 (M.op x y))) (M.op (M.op X2 (τ (σ x))) (M.op X2 (τ (σ x))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq287 eq9
    | exact resolve eq9 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq586 : ∀ X0 X1 X2 : G, (M.op X2 (τ (σ x))) = (M.op (M.op X1 (M.op X0 (M.op x y))) (k (M.op X2 (τ (σ x))) (M.op X2 (τ (σ x))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq585 X0 X1 X2
       have i₂ := eq83 (M.op X2 (τ sF4))
       grind)
    | exact superpose eq83 eq585
    | exact resolve eq585 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq605 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 (M.op X0 x) x
       have i₂ := eq83 (M.op X0 x)
       grind)
    | exact superpose eq83 eq62
    | exact resolve eq62 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq640 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq62 X1 X4 X0 X2
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq641 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq640 X0 X1 X2 X3 X4
       have i₂ := eq83 (M.op X4 X1)
       grind)
    | exact superpose eq83 eq640
    | exact resolve eq640 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq650 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq629 X0 X1 X2
       have i₂ := eq83 (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq83 eq629
    | exact resolve eq629 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq674 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (k (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq605 X0 X1 X2
       have i₂ := eq83 (M.op X1 (M.op (M.op X0 X0) X2))
       grind)
    | exact superpose eq83 eq605
    | exact resolve eq605 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq689 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 X0) X2)) = (M.op X0 (k (M.op X1 (M.op (k X0 X0) X2)) (M.op X1 (M.op (k X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 X0 X1 X2
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq674
    | exact resolve eq674 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq706 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ x)) (τ (σ x))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq373 (τ sF4)
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq373
    | exact resolve eq373 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq773 : ∀ X0 : G, (M.op X0 (τ (σ x))) = (M.op (M.op x y) (k (M.op X0 (τ (σ x))) (M.op X0 (τ (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq586 sF2 (M.op x (M.op sF2 x)) x
       have i₂ := eq9 sF2 x x
       grind)
    | exact superpose eq9 eq586
    | exact resolve eq586 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq809 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 (M.op X0 (τ (σ x)))) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq773 eq9
    | exact resolve eq9 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq810 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 (M.op X0 (τ (σ x)))) (k (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq809
    | exact resolve eq809 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq830 : (M.op x y) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq63 eq810
    | exact resolve eq810 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq810
  have eq1262 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq184 eq15
    | exact resolve eq15 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1275 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1262
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1262
    | exact resolve eq1262 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1276 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1275
    | exact resolve eq1275 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1341 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1276 eq15
    | exact resolve eq15 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1346 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1341
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1341
    | exact resolve eq1341 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq1347 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1346
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1346
    | exact resolve eq1346 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1348 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq1347
    | exact resolve eq1347 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1538 : (τ (σ x)) = (M.op (τ (σ x)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1348 eq340
    | exact resolve eq340 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1620 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq267 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq267
    | exact resolve eq267 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1629 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq267 (k X0 X0) (M.op x X0)
       have i₂ := eq267 X0 x
       grind)
    | exact superpose eq267 eq267
    | exact resolve eq267 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1641 : (τ (σ y)) = (M.op (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq42 eq267
    | exact resolve eq267 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) := by
    first
    | exact superpose eq32 eq267
    | (have j0 := eq267 (σ y) (σ x)
       grind)
    | exact resolve eq267 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1688 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1620 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq1620
    | exact resolve eq1620 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1698 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (σ y))) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1641 eq9
    | exact resolve eq9 eq1641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq1715 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (σ y))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1698 X0
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq1698
    | exact resolve eq1698 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698
  have eq1722 : (M.op x y) = (M.op (k (τ (σ y)) (τ (σ y))) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1715 (τ sF5)
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq1715
    | exact resolve eq1715 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1715
  have eq1785 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    intro X0
    first
    | exact superpose eq1722 eq9
    | exact resolve eq9 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq1803 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (M.op x y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1785 X0
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq1785
    | exact resolve eq1785 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1807 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (M.op x y)) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1803 X0
       have i₂ := eq1688 (τ sF5)
       grind)
    | exact superpose eq1688 eq1803
    | exact resolve eq1803 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1814 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1538 eq1807
    | exact resolve eq1807 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq1807
  have eq1837 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq42 eq1814
    | exact resolve eq1814 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq2280 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq349 (k (M.op X0 X1) (M.op X0 X1)) (k X0 X0)
       have i₂ := eq349 X0 X1
       grind)
    | exact superpose eq349 eq349
    | exact resolve eq349 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2281 : ∀ X0 : G, (k (τ (σ x)) (τ (σ x))) = (M.op (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) := by
    intro X0
    first
    | exact superpose eq578 eq349
    | exact resolve eq349 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq2282 : (k (τ (σ x)) (τ (σ x))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) := by
    first
    | exact superpose eq706 eq349
    | exact resolve eq349 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq2308 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X0)) ≠ X0 ∨ (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq349 X0 X1
       grind)
    | exact superpose eq349 eq13
    | (have j0 := eq13 (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq13 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2325 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) ≠ X0 ∨ (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2308 X0 X1
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq2308
    | (have j0 := eq2308 X0 X1
       grind)
    | exact resolve eq2308 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq2334 : (k (τ (σ x)) (τ (σ x))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) := by
    first
    | (have i₁ := eq2282
       have i₂ := eq1688 (τ sF4)
       grind)
    | exact superpose eq1688 eq2282
    | exact resolve eq2282 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2335 : ∀ X0 : G, (k (τ (σ x)) (τ (σ x))) = (M.op (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) (τ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq2281 X0
       have i₂ := eq1688 (τ sF4)
       grind)
    | exact superpose eq1688 eq2281
    | exact resolve eq2281 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq2336 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2280 X0 X1
       have i₂ := eq1688 (M.op X0 X1)
       grind)
    | exact superpose eq1688 eq2280
    | exact resolve eq2280 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq2350 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2325 X0 X1
       grind)
    | (have r₁ := eq2325 X0 X1
       have r₂ := eq1688 X0
       grind)
    | exact resolve eq2325 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2354 : (k (τ (σ x)) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | (have i₁ := eq2334
       have i₂ := eq1688 sF2
       grind)
    | exact superpose eq1688 eq2334
    | exact resolve eq2334 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2334
  have eq2356 : ∀ X0 X1 : G, (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2350 X0 X1
       have i₂ := eq83 (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq83 eq2350
    | (have j0 := eq2350 X0 X1
       grind)
    | exact resolve eq2350 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2357 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2356 X0 X1
       have i₂ := eq1688 (M.op X0 X1)
       grind)
    | exact superpose eq1688 eq2356
    | (have j0 := eq2356 X0 X1
       grind)
    | exact resolve eq2356 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356
  have eq2422 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) := by
    first
    | exact superpose eq830 eq350
    | (have j0 := eq350 (τ (σ x)) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq350 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq2451 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) := by
    first
    | (have i₁ := eq2422
       have i₂ := eq1688 sF2
       grind)
    | exact superpose eq1688 eq2422
    | exact resolve eq2422 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq3064 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq351
    | (have j0 := eq351 (σ y) (σ x)
       grind)
    | exact resolve eq351 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3394 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (σ y) X2))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq32 eq641
    | (have j0 := eq641 X1 (σ y) X2 X0 (σ x)
       grind)
    | exact resolve eq641 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq6132 : ∀ X0 X1 : G, (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) = (M.op X0 (k (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq689 X0 (M.op (k X0 X0) x) x
       have i₂ := eq83 (M.op (k X0 X0) x)
       grind)
    | exact superpose eq83 eq689
    | exact resolve eq689 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq689
  have eq6184 : ∀ X0 X1 : G, (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6132 X0 X1
       have i₂ := eq1688 (M.op (k X0 X0) X1)
       grind)
    | exact superpose eq1688 eq6132
    | exact resolve eq6132 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6132
  have eq6678 : ∀ X0 : G, (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) = (M.op (M.op x y) (k (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq42 eq650
    | exact resolve eq650 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6734 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X2 (M.op X1 X0)) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq650 (M.op X1 X0) (k X0 X0) X2
       have i₂ := eq267 X0 X1
       grind)
    | exact superpose eq267 eq650
    | exact resolve eq650 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq6932 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X2 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6734 X0 X1 X2
       have i₂ := eq1688 X0
       grind)
    | exact superpose eq1688 eq6734
    | exact resolve eq6734 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734
  have eq6986 : ∀ X0 : G, (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq6678 X0
       have i₂ := eq1688 (M.op (τ sF5) X0)
       grind)
    | exact superpose eq1688 eq6678
    | exact resolve eq6678 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6678
  have eq49458 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (k (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq2335 eq349
    | exact resolve eq349 eq2335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq49559 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq49458 X0
       have i₂ := eq1688 (M.op X0 sF2)
       grind)
    | exact superpose eq1688 eq49458
    | exact resolve eq49458 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49458
  have eq49618 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op (τ (σ x)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq49559 X0
       have i₂ := eq1688 (τ sF4)
       grind)
    | exact superpose eq1688 eq49559
    | exact resolve eq49559 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49559
  have eq54470 : ∀ X0 : G, (k X0 X0) = (M.op (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) X0) := by
    intro X0
    first
    | exact superpose eq6986 eq6932
    | exact resolve eq6932 eq6986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6932 eq6986
  have eq57701 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 (k (M.op (σ y) X0) (M.op (σ y) X0))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq54470 eq3394
    | exact resolve eq3394 eq54470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3394 eq54470
  have eq57909 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (k (σ y) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq57701 (k sF5 sF5) x
       have i₂ := eq340 sF5
       grind)
    | exact superpose eq340 eq57701
    | exact resolve eq57701 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq58228 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1653 eq57909
    | exact resolve eq57909 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57909
  have eq59321 : (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (σ y) (σ y))) := by
    first
    | exact superpose eq58228 eq349
    | exact resolve eq349 eq58228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58228
  have eq59976 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ y) (σ y)) (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq59321 eq349
    | exact resolve eq349 eq59321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60098 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq59976
       have i₂ := eq1688 sF6
       grind)
    | exact superpose eq1688 eq59976
    | exact resolve eq59976 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59976
  have eq65536 : (k (σ y) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq1653 eq2336
    | exact resolve eq2336 eq1653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq66068 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq182 eq3064
    | (have r₁ := eq3064
       have r₂ := eq182
       grind)
    | exact resolve eq3064 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq3064
  have eq66069 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq66068
  have eq66070 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq66069
       have r₂ := eq573
       grind)
    | exact resolve eq66069 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq66069
  have eq85448 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 (k (k (M.op (k (σ y) (σ y)) X0) (M.op (k (σ y) (σ y)) X0)) (k (M.op (k (σ y) (σ y)) X0) (M.op (k (σ y) (σ y)) X0)))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq57701 (M.op (k sF5 sF5) X1) X1
       have i₂ := eq6184 sF5 X1
       grind)
    | exact superpose eq6184 eq57701
    | exact resolve eq57701 eq6184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6184 eq57701
  have eq85460 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 (M.op (k (σ y) (σ y)) X0)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq85448 X0 X1
       have i₂ := eq1688 (M.op (k sF5 sF5) X0)
       grind)
    | exact superpose eq1688 eq85448
    | exact resolve eq85448 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85448
  have eq85746 : ∀ X0 X1 X2 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X0 (M.op (k (σ y) (σ y)) X1))) (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq85460 eq650
    | exact resolve eq650 eq85460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq85460
  have eq85875 : ∀ X0 X1 X2 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X2 (M.op X0 (M.op (k (σ y) (σ y)) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq85746 X0 X1 X2
       have i₂ := eq1688 sF6
       grind)
    | exact superpose eq1688 eq85746
    | exact resolve eq85746 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85746
  have eq86619 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (k (σ y) (σ y)) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq85875 (M.op (k sF5 sF5) x) x (M.op x (M.op (M.op (k sF5 sF5) x) x))
       have i₂ := eq9 (M.op (k sF5 sF5) x) x x
       grind)
    | exact superpose eq9 eq85875
    | exact resolve eq85875 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85875
  have eq86899 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq86619 (k (k (k sF5 sF5) (k sF5 sF5)) (k (k sF5 sF5) (k sF5 sF5)))
       have i₂ := eq1629 (k sF5 sF5)
       grind)
    | exact superpose eq1629 eq86619
    | exact resolve eq86619 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq87096 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq86899
       have i₂ := eq1688 sF5
       grind)
    | exact superpose eq1688 eq86899
    | exact resolve eq86899 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86899
  have eq87451 : (k (σ y) (σ y)) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq87096 eq350
    | (have j0 := eq350 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq350 eq87096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq87452 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq87096 eq351
    | (have j0 := eq351 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq351 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq87096
       grind)
    | exact resolve eq351 eq87096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq87096
  have eq87534 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq87452
  have eq87992 : (σ x) = (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq87534 eq396
    | exact resolve eq396 eq87534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq88627 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60098 eq2357
    | exact resolve eq2357 eq60098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60098
  have eq88642 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq2354 eq2357
    | exact resolve eq2357 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354 eq2357
  have eq88737 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq88642
       have i₂ := eq1688 (τ sF4)
       grind)
    | exact superpose eq1688 eq88642
    | exact resolve eq88642 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88642
  have eq88743 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq88627
       have i₂ := eq1688 sF6
       grind)
    | exact superpose eq1688 eq88627
    | exact resolve eq88627 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88627
  have eq88902 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq88743
       have i₂ := eq1688 sF5
       grind)
    | exact superpose eq1688 eq88743
    | exact resolve eq88743 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88743
  have eq96313 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq88902 eq87451
    | (have r₁ := eq87451
       have r₂ := eq88902
       grind)
    | exact resolve eq87451 eq88902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88902
  have eq96314 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq87534 eq87451
    | (have r₁ := eq87451
       have r₂ := eq87534
       grind)
    | exact resolve eq87451 eq87534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87451
  have eq96316 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq96314
  have eq96317 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq96313
  have eq96841 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq96316
  have eq97113 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq87992 eq86619
    | exact resolve eq86619 eq87992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86619 eq87992
  have eq97646 : (σ x) = (M.op (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq97113 eq349
    | exact resolve eq349 eq97113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97113
  have eq97779 : (σ x) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq97646
       have i₂ := eq1688 sF6
       grind)
    | exact superpose eq1688 eq97646
    | exact resolve eq97646 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97646
  have eq98409 : (k (σ x) (σ x)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq97779 eq2336
    | exact resolve eq2336 eq97779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336 eq97779
  have eq114541 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq87534 eq98409
    | exact resolve eq98409 eq87534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87534 eq98409
  have eq114686 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq114541
  have eq115754 : (k (σ y) (σ y)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq114686 eq349
    | exact resolve eq349 eq114686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq114686
  have eq115913 : (k (σ y) (σ y)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq115754
       have i₂ := eq1688 sF5
       grind)
    | exact superpose eq1688 eq115754
    | exact resolve eq115754 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115754
  have eq115952 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq115913
       have i₂ := eq1688 sF4
       grind)
    | exact superpose eq1688 eq115913
    | exact resolve eq115913 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115913
  have eq115965 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq32 eq115952
    | exact resolve eq115952 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115952
  have eq115973 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have r₁ := eq115965
       have r₂ := eq96841
       grind)
    | exact resolve eq115965 eq96841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96841 eq115965
  have eq116086 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq115973 eq96317
    | exact resolve eq96317 eq115973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96317 eq115973
  have eq370387 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1837 eq15
    | exact resolve eq15 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq370396 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq370387
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq370387
    | exact resolve eq370387 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370387
  have eq370418 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq370396
    | exact resolve eq370396 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370396
  have eq370419 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq370418
  have eq370427 : (k (M.op x y) (M.op x y)) = (τ (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq370419 eq72
    | exact resolve eq72 eq370419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq370430 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq370419 eq572
    | (have r₁ := eq572
       have r₂ := eq370419
       grind)
    | exact resolve eq572 eq370419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq370846 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  have eq370848 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq370430
  have eq371123 : (k (M.op x y) (M.op x y)) = (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq370427
       have i₂ := eq127 (k sF5 sF5) (k sF5 sF5)
       grind)
    | exact superpose eq127 eq370427
    | exact resolve eq370427 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370427
  have eq371204 : (k (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq371123
       have i₂ := eq127 sF5 sF5
       grind)
    | exact superpose eq127 eq371123
    | exact resolve eq371123 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371123
  have eq371224 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq371204
       have i₂ := eq1688 (τ sF5)
       grind)
    | exact superpose eq1688 eq371204
    | exact resolve eq371204 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371204
  have eq371945 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq371224 eq35
    | exact resolve eq35 eq371224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371224
  have eq371951 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq371945
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq371945
    | exact resolve eq371945 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371945
  have eq372005 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq371951
    | exact resolve eq371951 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371951
  have eq372177 : (σ (σ y)) = (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq372005 eq15
    | exact resolve eq15 eq372005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383608 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ (M.op x y))) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq372177 eq48
    | exact resolve eq48 eq372177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq372177
  have eq383685 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq383608 x
       have i₂ := eq46 sF5 x
       grind)
    | exact superpose eq46 eq383608
    | exact resolve eq383608 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq383608
  have eq437938 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq370848 eq116086
    | exact resolve eq116086 eq370848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116086 eq370848
  have eq438036 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq437938
       have r₂ := eq88
       grind)
    | exact resolve eq437938 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437938
  have eq438052 : (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq438036
       have r₂ := eq370846
       grind)
    | exact resolve eq438036 eq370846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438036
  have eq797448 : (σ (k (M.op x y) (M.op x y))) = (k (σ (k (M.op x y) (M.op x y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq88737 eq15
    | exact resolve eq15 eq88737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88737
  have eq797451 : (σ (k (M.op x y) (M.op x y))) = (k (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq797448
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq797448
    | exact resolve eq797448 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797448
  have eq797452 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq797451
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq797451
    | exact resolve eq797451 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797451
  have eq797453 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq26 eq797452
    | exact resolve eq797452 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797452
  have eq797465 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq372005 eq797453
    | exact resolve eq797453 eq372005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372005 eq797453
  have eq919181 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq797465 eq2451
    | (have r₁ := eq2451
       have r₂ := eq797465
       grind)
    | exact resolve eq2451 eq797465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451 eq797465
  have eq919211 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq919181
  have eq1515977 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq919211 eq15
    | exact resolve eq15 eq919211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919211
  have eq1515980 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1515977
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1515977
    | exact resolve eq1515977 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1515977
  have eq1515981 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1515980
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1515980
    | exact resolve eq1515980 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515980
  have eq1515982 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1515981
    | exact resolve eq1515981 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515981
  have eq1515987 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1515982 eq383685
    | exact resolve eq383685 eq1515982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383685 eq1515982
  have eq1515990 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq1515987
  have eq1516007 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1515990 eq438052
    | exact resolve eq438052 eq1515990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438052
  have eq1516283 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1516007 eq370846
    | exact resolve eq370846 eq1516007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516007
  have eq1516446 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1516283
  have eq1516464 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1516446
       have r₂ := eq1515990
       grind)
    | exact resolve eq1516446 eq1515990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516446
  have eq1516473 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq370419 eq1516464
    | exact resolve eq1516464 eq370419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370419
  have eq1516702 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1516464
  have eq1516768 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1516473
       have r₂ := eq370846
       grind)
    | exact resolve eq1516473 eq370846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516473
  have eq1517037 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1516768 eq370846
    | exact resolve eq370846 eq1516768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370846 eq1516768
  have eq1517584 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq1517037
  have eq1517616 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1517584
       have r₂ := eq1515990
       grind)
    | exact resolve eq1517584 eq1515990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515990 eq1517584
  have eq1517642 : (M.op x y) = (τ (k (σ y) (σ x))) := by
    first
    | exact superpose eq1517616 eq36
    | exact resolve eq36 eq1517616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1518292 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq1517642
       have i₂ := eq127 sF4 sF5
       grind)
    | exact superpose eq127 eq1517642
    | exact resolve eq1517642 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517642
  have eq2187320 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq66070 eq33
    | exact resolve eq33 eq66070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2187329 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2187320
       have r₂ := eq1517616
       grind)
    | exact resolve eq2187320 eq1517616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187320
  have eq2187335 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2187329 eq88
    | (have r₁ := eq88
       have r₂ := eq2187329
       grind)
    | exact resolve eq88 eq2187329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq2187366 : (k (σ y) (σ y)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2187329 eq65536
    | exact resolve eq65536 eq2187329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65536 eq2187329
  have eq2187470 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq2187335
  have eq2187494 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq2187366
       have i₂ := eq1688 sF4
       grind)
    | exact superpose eq1688 eq2187366
    | exact resolve eq2187366 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187366
  have eq2187513 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq2187494
    | exact resolve eq2187494 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187494
  have eq2187518 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2187513 eq33
    | exact resolve eq33 eq2187513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187513
  have eq2187693 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1517616 eq2187518
    | exact resolve eq2187518 eq1517616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187518
  have eq2187699 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2187693
       have r₂ := eq2187470
       grind)
    | exact resolve eq2187693 eq2187470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187470 eq2187693
  have eq2192576 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2187699 eq1516702
    | (have r₁ := eq1516702
       have r₂ := eq2187699
       grind)
    | exact resolve eq1516702 eq2187699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516702
  have eq2192863 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq2187699 eq127
    | exact resolve eq127 eq2187699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq2192887 : (σ (M.op x y)) = (σ y) := by grind
  clear eq2192576
  have eq2192893 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq1518292 eq2192863
    | exact resolve eq2192863 eq1518292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518292 eq2192863
  have eq2197890 : (M.op x y) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq2192893 eq42
    | exact resolve eq42 eq2192893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq2192893
  have eq2200929 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (M.op x y)) := by
    first
    | exact superpose eq2197890 eq49618
    | exact resolve eq49618 eq2197890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49618
  have eq2201330 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2197890 eq2200929
    | exact resolve eq2200929 eq2197890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197890 eq2200929
  have eq2203000 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2201330 eq15
    | exact resolve eq15 eq2201330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201330
  have eq2203070 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq2203000
    | exact resolve eq2203000 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2203000
  have eq2203289 : (k (σ y) (σ x)) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq1517616 eq2203070
    | exact resolve eq2203070 eq1517616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517616 eq2203070
  have eq2203362 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2187699 eq2203289
    | exact resolve eq2203289 eq2187699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203289
  have eq2203372 : (σ y) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq2203362 eq574
    | exact resolve eq574 eq2203362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq2203441 : (σ y) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2203362 eq59321
    | exact resolve eq59321 eq2203362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59321 eq2203362
  have eq2205181 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2203372
       have r₂ := eq66070
       grind)
    | exact resolve eq2203372 eq66070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66070 eq2203372
  have eq2205279 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2187699 eq2205181
    | exact resolve eq2205181 eq2187699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187699 eq2205181
  have eq2223521 : (σ y) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2205279 eq2203441
    | exact resolve eq2203441 eq2205279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203441 eq2205279
  have eq2223528 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2223521
       have i₂ := eq1688 sF4
       grind)
    | exact superpose eq1688 eq2223521
    | exact resolve eq2223521 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688 eq2223521
  have eq2223676 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq2223528
    | exact resolve eq2223528 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2223528
  have eq2223677 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2223676
  have eq2223733 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2223677 eq33
    | exact resolve eq33 eq2223677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq2223677
  have eq2227179 : False := by grind
  exact eq2227179

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
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
  have eq86 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq42 eq15
    | exact resolve eq15 eq42
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
  have eq100 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq45
    | (have j0 := eq45 (M.op x y)
       grind)
    | exact resolve eq45 eq20
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
  have eq164 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq86
    | exact resolve eq86 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq13
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq178 X0
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq183 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq188 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | (have i₁ := eq42 (M.op sF0 sF0)
       have i₂ := eq185 sF0
       grind)
    | exact superpose eq185 eq42
    | exact resolve eq42 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq188
    | exact resolve eq188 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq200 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 x) (M.op (M.op X1 (M.op x y)) (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq209 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq184 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq184
    | (have j0 := eq184 y x
       grind)
    | exact resolve eq184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq185 (M.op X0 X0)
       have i₂ := eq184 X0 X0
       grind)
    | exact superpose eq184 eq185
    | exact resolve eq185 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178 (M.op X0 X0)
       have i₂ := eq184 X0 X0
       grind)
    | exact superpose eq184 eq178
    | exact resolve eq178 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq184 X0 X1
       grind)
    | exact superpose eq184 eq13
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq209 eq16
    | exact resolve eq16 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq257 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq142 (M.op sF2 sF2)
       have i₂ := eq185 sF2
       grind)
    | exact superpose eq185 eq142
    | exact resolve eq142 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq30 eq257
    | exact resolve eq257 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq406 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq551 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 (k X0 X0)
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (k X0 X1)) (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 (M.op X0 X2))) ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
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
  have eq577 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq584 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq611 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq568
       grind)
    | exact superpose eq568 eq40
    | exact resolve eq40 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq611
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq611
    | exact resolve eq611 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq614 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq612
    | exact resolve eq612 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq621 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq584 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq584
    | (have j0 := eq584 (σ X0)
       grind)
    | exact resolve eq584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq614 eq577
    | exact resolve eq577 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq679 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq672
       have r₂ := eq27
       grind)
    | exact resolve eq672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq684 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq679
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq679
       grind)
    | exact resolve eq12 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq184
    | exact resolve eq184 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq679
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq679
       grind)
    | exact resolve eq13 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq689 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq687
  have eq690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq684
  have eq691 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq690
    | exact resolve eq690 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq693 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq689 eq91
    | exact resolve eq91 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq696 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq693
    | exact resolve eq693 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq708 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq686 eq28
    | (have j0 := eq28 (M.op (σ x) (σ x)) (σ y)
       grind)
    | exact resolve eq28 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : (σ x) ≠ (σ y) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq686 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq686
       grind)
    | exact resolve eq13 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq686 eq16
    | exact resolve eq16 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq691 eq614
    | exact resolve eq614 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq718 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq691 eq142
    | exact resolve eq142 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq719 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq714
  have eq721 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq718
    | exact resolve eq718 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq724 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq568 eq721
    | exact resolve eq721 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq731 : x = (M.op y (M.op x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184 x y
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq184
    | exact resolve eq184 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : y ≠ y ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq719
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq719
       grind)
    | exact resolve eq13 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq734 : y = (k x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq732
  have eq746 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq734
       grind)
    | exact superpose eq734 eq36
    | exact resolve eq36 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734
  have eq749 : (σ y) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq746
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq746
    | exact resolve eq746 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq777 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 (M.op x x)
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq16
    | exact resolve eq16 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq796 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op (M.op X0 (σ y)) (M.op (M.op X1 (σ x)) (M.op X1 (σ x)))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq711 eq16
    | exact resolve eq16 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq849 : ∀ X0 X1 : G, (M.op X1 x) = (M.op (M.op X0 y) (M.op (M.op X1 x) (M.op X1 x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 x) X0 (M.op y y)
       have i₂ := eq777 X1
       grind)
    | exact superpose eq777 eq16
    | exact resolve eq16 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq960 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (σ y)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq796 X0 sF2
       have i₂ := eq184 sF2 sF2
       grind)
    | exact superpose eq184 eq796
    | exact resolve eq796 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq972 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq960
    | (have j0 := eq960 (σ x)
       grind)
    | exact resolve eq960 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : (M.op (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq972 eq28
    | (have j0 := eq28 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq972 eq16
    | exact resolve eq16 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1011 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq686 eq996
    | exact resolve eq996 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1020 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by grind
  clear eq1011
  have eq1043 : (σ x) = (k (k (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq993 eq185
    | exact resolve eq185 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : (σ x) = (M.op (σ x) (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq993 eq178
    | exact resolve eq178 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq993 eq28
    | (have j0 := eq28 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : (σ x) = (M.op (k (σ x) (M.op (σ x) (σ y))) (k (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq993 eq184
    | exact resolve eq184 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1049 : (σ x) ≠ (k (σ x) (M.op (σ x) (σ y))) ∨ (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq993 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq993
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq993
       grind)
    | exact resolve eq13 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1057 : (k (σ x) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1047
       have r₂ := eq1049
       grind)
    | exact resolve eq1047 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq1049
  have eq1087 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1057 eq1044
    | exact resolve eq1044 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1088 : (σ x) = (k (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1057 eq1043
    | exact resolve eq1043 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043
  have eq1092 : (σ x) = (k (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq1088
  have eq1093 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq1087
  have eq1255 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ (k X0 X1))) (M.op (σ X1) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 (σ X0) (σ X1) X2
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq554
    | (have j0 := eq554 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1398 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq608 x y
       have i₂ := eq696
       grind)
    | exact superpose eq696 eq608
    | (have j0 := eq608 x y
       grind)
    | (have r₁ := eq608 x y
       have r₂ := eq696
       grind)
    | exact resolve eq608 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1404 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq749 eq608
    | (have j0 := eq608 (σ x) (σ y)
       grind)
    | (have r₁ := eq608 (σ x) (σ y)
       have r₂ := eq749
       grind)
    | exact resolve eq608 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq1415 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1404
  have eq1418 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq1398
  have eq1434 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1415
    | exact resolve eq1415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq1435 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1434
  have eq1438 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1418
    | exact resolve eq1418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1449 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq568 eq1438
    | exact resolve eq1438 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1455 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1449
       grind)
    | exact superpose eq1449 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1449
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1449
       grind)
    | exact resolve eq12 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1461 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1455
  have eq1463 : x = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1461
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1461
    | exact resolve eq1461 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1464 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1463
  have eq1476 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1464
       grind)
    | exact superpose eq1464 eq40
    | exact resolve eq40 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1481 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1476
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1476
    | exact resolve eq1476 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq2055 : (σ x) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1057 eq1048
    | exact resolve eq1048 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2068 : ∀ X0 : G, (k (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1048 eq16
    | exact resolve eq16 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq2075 : (σ x) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq2055
  have eq2080 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1057 eq2068
    | exact resolve eq2068 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq2068
  have eq2332 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq2080
    | exact resolve eq2080 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2367 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq2332
  have eq2379 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq2367
    | exact resolve eq2367 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367
  have eq2383 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2379 eq98
    | exact resolve eq98 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2386 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2379 eq1092
    | exact resolve eq1092 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq2387 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2379 eq1093
    | exact resolve eq1093 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq2393 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2379 eq2075
    | exact resolve eq2075 eq2379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075 eq2379
  have eq2401 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq2393
  have eq2407 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq2387
  have eq2408 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq2386
  have eq2415 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq2407
    | exact resolve eq2407 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq2416 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq614 eq2408
    | exact resolve eq2408 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408
  have eq2417 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq2383
    | exact resolve eq2383 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2428 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2415 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq2415
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2415
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2415
       grind)
    | exact resolve eq12 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2437 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2428
  have eq2440 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2416 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq2416
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2416
       grind)
    | exact resolve eq12 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2449 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq2440
  have eq2497 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2401 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq2401
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2401
       grind)
    | exact resolve eq13 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2499 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2401 eq28
    | (have j0 := eq28 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2501 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2401 eq184
    | exact resolve eq184 eq2401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2508 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq2497
       have r₂ := eq2499
       grind)
    | exact resolve eq2497 eq2499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2497 eq2499
  have eq2532 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2501 eq278
    | exact resolve eq278 eq2501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq2594 : x = (k y x) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq2532
    | exact resolve eq2532 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq2597 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq568 eq2594
    | exact resolve eq2594 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2594
  have eq2629 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2661 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq177 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 y x X0 X1
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2717 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2829 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq177 X1 X4 X0 X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2995 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)))) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X0 X0 X1
       have i₂ := eq562 X0 (M.op X0 (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq562 eq177
    | (have j1 := eq562 X0 (M.op X0 (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact resolve eq177 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq3001 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have i₂ := eq562 X0 X1 X2
       grind)
    | exact superpose eq562 eq12
    | (have j0 := eq12 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have j1 := eq562 X0 X1 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have r₂ := eq562 X0 X1 X2
       grind)
    | exact resolve eq12 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq3012 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3001 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3001
  have eq3014 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3012 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq3012
    | (have j0 := eq3012 X0 X1 X2
       grind)
    | exact resolve eq3012 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3012
  have eq3030 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3014 X0 X1 X2
       have j1 := eq181 X0 X1 X2
       grind)
    | (have r₁ := eq3014 X0 X1 X2
       have r₂ := eq181 X0 X1 X2
       grind)
    | exact resolve eq3014 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3014
  have eq3063 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2508 eq116
    | exact resolve eq116 eq2508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq3073 : x = (k y y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq3063
    | exact resolve eq3063 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063
  have eq3076 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2597 eq3073
    | exact resolve eq3073 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq3629 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2437 eq972
    | exact resolve eq972 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3651 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2437 eq184
    | exact resolve eq184 eq2437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437
  have eq3671 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3629
  have eq3679 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2449 eq972
    | exact resolve eq972 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq3695 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2449 eq13
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq2449
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2449
       grind)
    | exact resolve eq13 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3701 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2449 eq184
    | exact resolve eq184 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq3706 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq3695
  have eq3719 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3679
  have eq3813 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3671 eq184
    | exact resolve eq184 eq3671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq3862 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq3706
  have eq3922 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3719 eq184
    | exact resolve eq184 eq3719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq5543 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq708 eq12
    | (have j0 := eq12 (M.op (σ x) (σ x)) (σ y)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ x)) (σ y)
       have r₂ := eq708
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq708
       grind)
    | exact resolve eq12 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq5556 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq5543
  have eq5572 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq686 eq5556
    | exact resolve eq5556 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq5556
  have eq5576 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq5572
       have r₂ := eq710
       grind)
    | exact resolve eq5572 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq5572
  have eq5607 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3651 eq16
    | exact resolve eq16 eq3651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3651
  have eq5635 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3813 eq5607
    | exact resolve eq5607 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3813 eq5607
  have eq5676 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3701 eq16
    | exact resolve eq16 eq3701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5703 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq3922 eq5676
    | exact resolve eq5676 eq3922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922 eq5676
  have eq6272 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq5635
    | exact resolve eq5635 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq6348 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq6272
  have eq6370 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq6348
    | exact resolve eq6348 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq6533 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq5703
    | exact resolve eq5703 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq6607 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq6533
  have eq6626 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq679 eq6607
    | exact resolve eq6607 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6607
  have eq7802 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by grind
  have eq7811 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (k (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq13 eq7802
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7802
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7802 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7802
  have eq7832 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (k (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7811
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq7811
    | (have j1 := eq28 y x
       grind)
    | (have r₁ := eq7811
       have r₂ := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq7811 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7841 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (k (σ x) (σ x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq7832
       have r₂ := eq7811
       grind)
    | exact resolve eq7832 eq7811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7811 eq7832
  have eq7988 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq849 X0 x
       have i₂ := eq184 x x
       grind)
    | exact superpose eq184 eq849
    | exact resolve eq849 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq8025 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7988 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7988
    | (have j0 := eq7988 x
       grind)
    | exact resolve eq7988 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7988
  have eq8074 : x = (M.op x (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq8025
       grind)
    | exact superpose eq8025 eq178
    | exact resolve eq178 eq8025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8076 : x = (k (M.op (M.op x y) x) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq185 x
       have i₂ := eq8025
       grind)
    | exact superpose eq8025 eq185
    | exact resolve eq185 eq8025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8083 : x ≠ (M.op (M.op x y) x) ∨ (k x x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq8025
       grind)
    | exact superpose eq8025 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8025
       grind)
    | exact resolve eq13 eq8025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8085 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq8025
       grind)
    | exact superpose eq8025 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq8025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8089 : x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184 x x
       have i₂ := eq8025
       grind)
    | exact superpose eq8025 eq184
    | exact resolve eq184 eq8025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8025
  have eq8103 : (k x x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8083
       have r₂ := eq8085
       grind)
    | exact resolve eq8083 eq8085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8083 eq8085
  have eq8166 : x = (k (k x x) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8103 eq8076
    | exact resolve eq8076 eq8103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8076
  have eq8167 : x = (M.op x (k x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8103 eq8074
    | exact resolve eq8074 eq8103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8074
  have eq8197 : x = (M.op x (k x x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8167
  have eq8198 : x = (k (k x x) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8166
  have eq8527 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 x) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8089 eq16
    | exact resolve eq16 eq8089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8089
  have eq8546 : ∀ X0 : G, (k x x) = (M.op (M.op X0 x) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8103 eq8527
    | exact resolve eq8527 eq8103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8103 eq8527
  have eq8686 : (k x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8546 y
       have i₂ := eq719
       grind)
    | exact superpose eq719 eq8546
    | exact resolve eq8546 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8546
  have eq8727 : (k x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8686
  have eq8737 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq719 eq8727
    | exact resolve eq8727 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8727
  have eq8749 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8197
       have i₂ := eq8737
       grind)
    | exact superpose eq8737 eq8197
    | exact resolve eq8197 eq8737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8197
  have eq8750 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8198
       have i₂ := eq8737
       grind)
    | exact superpose eq8737 eq8198
    | exact resolve eq8198 eq8737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8757 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq8737
       grind)
    | exact superpose eq8737 eq40
    | exact resolve eq40 eq8737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8737
  have eq8766 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8750
  have eq8767 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8749
  have eq8776 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8757
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8757
    | exact resolve eq8757 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8757
  have eq8778 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8767
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8767
    | exact resolve eq8767 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8767
  have eq8781 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8776
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8776
    | exact resolve eq8776 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq8791 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8778 eq27
    | exact resolve eq27 eq8778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8793 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8778 eq180
    | (have r₁ := eq180
       have r₂ := eq8778
       grind)
    | exact resolve eq180 eq8778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8778
  have eq8902 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8793
  have eq9108 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq8766
       grind)
    | exact superpose eq8766 eq37
    | exact resolve eq37 eq8766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8766
  have eq9122 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9108
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9108
    | exact resolve eq9108 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9108
  have eq9277 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8781 eq551
    | (have j0 := eq551 (σ x)
       grind)
    | exact resolve eq551 eq8781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8781
  have eq9286 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq9277
    | exact resolve eq9277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9277
  have eq9287 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9286
  have eq9310 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8902 eq614
    | exact resolve eq614 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9316 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8902 eq1481
    | exact resolve eq1481 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9317 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8902 eq108
    | exact resolve eq108 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq8902
  have eq9322 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9316
  have eq9331 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq9317
    | exact resolve eq9317 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9317
  have eq9332 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9310
       have r₂ := eq8791
       grind)
    | exact resolve eq9310 eq8791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9310
  have eq9430 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9122 eq1435
    | exact resolve eq1435 eq9122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1435 eq9122
  have eq9439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9430
  have eq9457 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9439 eq27
    | exact resolve eq27 eq9439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9459 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9439 eq180
    | (have r₁ := eq180
       have r₂ := eq9439
       grind)
    | exact resolve eq180 eq9439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq9462 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9439 eq605
    | (have r₁ := eq605
       have r₂ := eq9439
       grind)
    | exact resolve eq605 eq9439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq9528 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9439 eq6626
    | exact resolve eq6626 eq9439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9546 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9528
  have eq9556 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9462
  have eq9557 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9459
  have eq9617 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9287 eq3701
    | exact resolve eq3701 eq9287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3701
  have eq9705 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq9617
       have r₂ := eq3862
       grind)
    | exact resolve eq9617 eq3862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3862 eq9617
  have eq9710 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6626 eq9705
    | exact resolve eq9705 eq6626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6626 eq9705
  have eq9712 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq719 eq9710
    | exact resolve eq9710 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9710
  have eq9713 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9546 eq9712
    | exact resolve eq9712 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546 eq9712
  have eq9714 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have j1 := eq584 (σ x)
       grind)
    | (have r₁ := eq9713
       have r₂ := eq584 (σ x)
       grind)
    | exact resolve eq9713 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9713
  have eq9796 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9332
       grind)
    | exact superpose eq9332 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9332
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq9332
       grind)
    | exact resolve eq12 eq9332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9809 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq9796
  have eq9824 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9809
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9809
    | exact resolve eq9809 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9809
  have eq9825 : x = (M.op x y) ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9824
  have eq9826 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9331 eq9825
    | exact resolve eq9825 eq9331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9331 eq9825
  have eq9827 : (M.op x y) = (τ (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9826 eq29
    | exact resolve eq29 eq9826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9831 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9826 eq86
    | exact resolve eq86 eq9826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq9832 : (k x (M.op x y)) = (τ (k (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9826 eq100
    | exact resolve eq100 eq9826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq9835 : (k (M.op x y) x) = (τ (k (σ y) (σ x))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq9826 eq132
    | exact resolve eq132 eq9826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9844 : (k y x) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq9835
    | exact resolve eq9835 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9835
  have eq9847 : (k x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq9832
    | exact resolve eq9832 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq9832
  have eq9848 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq73 eq9831
    | exact resolve eq9831 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq9831
  have eq9852 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq9827
    | exact resolve eq9827 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9827
  have eq10051 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9557 eq614
    | exact resolve eq614 eq9557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10077 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq10051
       have r₂ := eq9457
       grind)
    | exact resolve eq10051 eq9457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10051
  have eq10303 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq10077
       grind)
    | exact superpose eq10077 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq10077
       grind)
    | exact resolve eq13 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10309 : x = (M.op y (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq184 x y
       have i₂ := eq10077
       grind)
    | exact superpose eq10077 eq184
    | exact resolve eq184 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10314 : y = (k x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10303
  have eq10396 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq10314
       grind)
    | exact superpose eq10314 eq36
    | exact resolve eq36 eq10314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10314
  have eq10404 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq10396
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10396
    | exact resolve eq10396 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10396
  have eq10441 : (k y x) = (τ (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9322 eq115
    | exact resolve eq115 eq9322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10481 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9322 eq1481
    | exact resolve eq1481 eq9322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10549 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10481
  have eq10566 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9826 eq10549
    | exact resolve eq10549 eq9826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10549
  have eq10567 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10566
  have eq10579 : (k x x) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq98 eq10441
    | exact resolve eq10441 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10441
  have eq10598 : y = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1464 eq10579
    | exact resolve eq10579 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq10579
  have eq10602 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9852 eq10598
    | exact resolve eq10598 eq9852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9852 eq10598
  have eq10604 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9826 eq10602
    | exact resolve eq10602 eq9826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9826 eq10602
  have eq10605 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10604
  have eq10782 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq10605
       grind)
    | exact superpose eq10605 eq584
    | (have j0 := eq584 x
       grind)
    | (have r₁ := eq584 x
       have r₂ := eq10605
       grind)
    | exact resolve eq584 eq10605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10605
  have eq10784 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq10782
  have eq11369 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq568
       have i₂ := eq9844
       grind)
    | exact superpose eq9844 eq568
    | exact resolve eq568 eq9844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq9844
  have eq11396 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1449 eq11369
    | exact resolve eq11369 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11369
  have eq11397 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq11396
  have eq11411 : y = (k x (M.op x y)) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq696
       have i₂ := eq9847
       grind)
    | exact superpose eq9847 eq696
    | exact resolve eq696 eq9847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9847
  have eq11436 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1449 eq11411
    | exact resolve eq11411 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11411
  have eq11442 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1449 eq11436
    | exact resolve eq11436 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11436
  have eq11443 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq11442
  have eq11843 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq10309
       have i₂ := eq10784
       grind)
    | exact superpose eq10784 eq10309
    | exact resolve eq10309 eq10784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10309 eq10784
  have eq11870 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq11843
  have eq11872 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9322 eq11870
    | exact resolve eq11870 eq9322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9322 eq11870
  have eq12034 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11397 eq40
    | exact resolve eq40 eq11397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11397
  have eq12037 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12034
    | exact resolve eq12034 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034
  have eq12039 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9332 eq12037
    | exact resolve eq12037 eq9332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9332 eq12037
  have eq12041 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1481 eq12039
    | exact resolve eq12039 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq12039
  have eq12097 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12041 eq9557
    | exact resolve eq9557 eq12041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9557 eq12041
  have eq12103 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12097
  have eq12477 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12103 eq11872
    | exact resolve eq11872 eq12103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11872 eq12103
  have eq12515 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12477
  have eq14601 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9714 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq9714
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq9714
       grind)
    | exact resolve eq13 eq9714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq14610 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14601
  have eq14676 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10567 eq14610
    | exact resolve eq14610 eq10567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10567 eq14610
  have eq14757 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9556 eq184
    | exact resolve eq184 eq9556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14768 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10404 eq14757
    | exact resolve eq14757 eq10404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14757
  have eq14769 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14768
  have eq15028 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14676 eq584
    | (have j0 := eq584 (σ x)
       grind)
    | (have r₁ := eq584 (σ x)
       have r₂ := eq14676
       grind)
    | exact resolve eq584 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14676
  have eq15030 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15028
  have eq15220 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq15030 eq14769
    | exact resolve eq14769 eq15030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14769 eq15030
  have eq15278 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq15220
  have eq15305 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq15278
       have r₂ := eq9457
       grind)
    | exact resolve eq15278 eq9457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9457 eq15278
  have eq15572 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq15305 eq9556
    | exact resolve eq9556 eq15305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9556 eq15305
  have eq15619 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq15572
  have eq15638 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq10404 eq15619
    | exact resolve eq15619 eq10404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10404 eq15619
  have eq15639 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq15638
  have eq15659 : y ≠ y ∨ y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15639 eq13
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq15639
       grind)
    | exact resolve eq13 eq15639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15670 : y = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq15659
  have eq15682 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15670 eq38
    | exact resolve eq38 eq15670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670
  have eq15689 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq15682
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15682
    | exact resolve eq15682 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682
  have eq15694 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15689 eq608
    | (have j0 := eq608 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq608 (σ (M.op x y)) (σ y)
       have r₂ := eq15689
       grind)
    | exact resolve eq608 eq15689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689
  have eq15696 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq15694
  have eq15783 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq200 X0 sF0
       have i₂ := eq184 sF0 sF0
       grind)
    | exact superpose eq184 eq200
    | exact resolve eq200 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17161 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y))))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq679 eq203
    | exact resolve eq203 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq17420 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17161 sF4
       have i₂ := eq184 sF4 sF4
       grind)
    | exact superpose eq184 eq17161
    | exact resolve eq17161 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17161
  have eq17483 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17420 eq178
    | exact resolve eq178 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17485 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17420 eq185
    | exact resolve eq185 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq17492 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17420 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq17420
       grind)
    | exact resolve eq13 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17494 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17420 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17498 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17420 eq184
    | exact resolve eq184 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17515 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq17492
       have r₂ := eq17494
       grind)
    | exact resolve eq17492 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17492
  have eq17564 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq17485
    | exact resolve eq17485 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17485
  have eq17565 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq17483
    | exact resolve eq17483 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17483
  have eq17587 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq184
    | exact resolve eq184 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17601 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by grind
  clear eq17565
  have eq17602 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq17564
  have eq17603 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17420 eq17587
    | exact resolve eq17587 eq17420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17420 eq17587
  have eq17612 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq17603
    | exact resolve eq17603 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17603
  have eq17633 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17601 eq184
    | exact resolve eq184 eq17601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17601
  have eq17641 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17612 eq17633
    | exact resolve eq17633 eq17612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17612 eq17633
  have eq17656 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17641 eq1020
    | exact resolve eq1020 eq17641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq17641
  have eq17702 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by grind
  clear eq17656
  have eq18034 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17498 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq17498
       grind)
    | exact resolve eq13 eq17498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18035 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq17498 eq16
    | exact resolve eq16 eq17498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18036 : (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17498 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq17498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17498
  have eq18053 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17494 eq18036
    | exact resolve eq18036 eq17494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17494 eq18036
  have eq18054 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq17515 eq18035
    | exact resolve eq18035 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18035
  have eq18055 : (M.op (σ x) (σ y)) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq18034
    | exact resolve eq18034 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18034
  have eq18067 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq18053
    | exact resolve eq18053 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18053
  have eq18068 : (M.op (σ x) (σ y)) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq17515 eq18055
    | exact resolve eq18055 eq17515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17515 eq18055
  have eq18073 : (M.op (σ x) (σ y)) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq18068
       have r₂ := eq18067
       grind)
    | exact resolve eq18068 eq18067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18067 eq18068
  have eq18191 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2415 eq18054
    | exact resolve eq18054 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18192 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2416 eq18054
    | exact resolve eq18054 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18193 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2417 eq18054
    | exact resolve eq18054 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18194 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2597 eq18054
    | exact resolve eq18054 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18195 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3076 eq18054
    | exact resolve eq18054 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18054
  have eq18265 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by grind
  clear eq18195
  have eq18266 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq18194
  have eq18267 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (k x x) := by grind
  clear eq18193
  have eq18268 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18192
  have eq18269 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18191
  have eq18293 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq3076 eq18265
    | exact resolve eq18265 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076 eq18265
  have eq18294 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2597 eq18266
    | exact resolve eq18266 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2597 eq18266
  have eq18295 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (k x x) := by
    first
    | exact superpose eq2417 eq18267
    | exact resolve eq18267 eq2417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417 eq18267
  have eq18296 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2416 eq18268
    | exact resolve eq18268 eq2416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416 eq18268
  have eq18297 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2415 eq18269
    | exact resolve eq18269 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415 eq18269
  have eq18308 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18294 eq18295
    | exact resolve eq18295 eq18294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18295
  have eq18346 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18297 eq17602
    | exact resolve eq17602 eq18297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17602
  have eq18348 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18297 eq17702
    | exact resolve eq17702 eq18297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18297
  have eq18354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18348
  have eq18356 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18346
  have eq18777 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18354 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq18354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18787 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq18777
  have eq18883 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18356 eq6370
    | exact resolve eq6370 eq18356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6370 eq18356
  have eq18898 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18883
  have eq19530 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18294 eq17702
    | exact resolve eq17702 eq18294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17702 eq18294
  have eq19536 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq19530
  have eq19778 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18787 eq98
    | exact resolve eq98 eq18787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19843 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq18898 eq19778
    | exact resolve eq19778 eq18898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18898 eq19778
  have eq19846 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq19843
    | exact resolve eq19843 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19843
  have eq19849 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq724 eq19846
    | exact resolve eq19846 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq19846
  have eq20008 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19536 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19536
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19536
       grind)
    | exact resolve eq13 eq19536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19536
  have eq20074 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20008
       have r₂ := eq18787
       grind)
    | exact resolve eq20008 eq18787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18787 eq20008
  have eq20266 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq19849
       grind)
    | exact superpose eq19849 eq40
    | exact resolve eq40 eq19849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19849
  have eq20299 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq20266
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20266
    | exact resolve eq20266 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20304 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq20299
    | exact resolve eq20299 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20299
  have eq20308 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq719 eq20304
    | exact resolve eq20304 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq20304
  have eq20454 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20074 eq98
    | exact resolve eq98 eq20074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20074
  have eq20550 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20308 eq551
    | (have j0 := eq551 (σ x)
       grind)
    | exact resolve eq551 eq20308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20308
  have eq20586 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq20550
    | exact resolve eq20550 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20550
  have eq20587 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq20586
  have eq20704 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20587 eq18354
    | exact resolve eq18354 eq20587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18354 eq20587
  have eq20780 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20704
  have eq21696 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18296 eq18073
    | exact resolve eq18073 eq18296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18296
  have eq21704 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq21696
  have eq21710 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20780 eq21704
    | exact resolve eq21704 eq20780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21704
  have eq22884 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2717 x X1 X0
       have i₂ := eq184 x x
       grind)
    | exact superpose eq184 eq2717
    | exact resolve eq2717 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq23375 : (σ x) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq621 x
       have i₂ := eq20454
       grind)
    | exact superpose eq20454 eq621
    | (have j0 := eq621 x
       grind)
    | exact resolve eq621 eq20454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20454
  have eq23393 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23375
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq23375
    | exact resolve eq23375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23375
  have eq23403 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23393
    | exact resolve eq23393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23393
  have eq23409 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23403
       have r₂ := eq20780
       grind)
    | exact resolve eq23403 eq20780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23403
  have eq23410 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23409
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23409
    | exact resolve eq23409 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23409
  have eq23508 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23410 eq5576
    | exact resolve eq5576 eq23410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5576 eq23410
  have eq23601 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq23508
  have eq23823 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23601 eq153
    | exact resolve eq153 eq23601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq23601
  have eq23846 : x = (k x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq23823
    | exact resolve eq23823 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23823
  have eq23849 : x = (k x (M.op x y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1449 eq23846
    | exact resolve eq23846 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1449 eq23846
  have eq23852 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11443 eq23849
    | exact resolve eq23849 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443 eq23849
  have eq23853 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq23852
  have eq23882 : y ≠ y ∨ x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq23853
       grind)
    | exact superpose eq23853 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23853
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq23853
       grind)
    | exact resolve eq12 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23889 : x = (M.op y (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184 x y
       have i₂ := eq23853
       grind)
    | exact superpose eq23853 eq184
    | exact resolve eq184 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23895 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq23882
  have eq23909 : x = (M.op x y) ∨ y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23895
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23895
    | exact resolve eq23895 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895
  have eq23910 : y = (k y x) ∨ x = (M.op x y) := by grind
  clear eq23909
  have eq23955 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq23910
       grind)
    | exact superpose eq23910 eq40
    | exact resolve eq40 eq23910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23965 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23955
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23955
    | exact resolve eq23955 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23955
  have eq24043 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 (M.op x x)
       have i₂ := eq23889
       grind)
    | exact superpose eq23889 eq16
    | exact resolve eq16 eq23889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23889
  have eq25456 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18308 eq18073
    | exact resolve eq18073 eq18308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18308
  have eq25463 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq25456
  have eq25480 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20780 eq25463
    | exact resolve eq25463 eq20780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25463
  have eq25726 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25480 eq7841
    | (have r₁ := eq7841
       have r₂ := eq25480
       grind)
    | exact resolve eq7841 eq25480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7841
  have eq25735 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25480 eq142
    | exact resolve eq142 eq25480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25480
  have eq25748 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq25726
  have eq25749 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq25748
  have eq25770 : x = (k x x) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq25735
    | exact resolve eq25735 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25735
  have eq25777 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23853 eq25770
    | exact resolve eq25770 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25770
  have eq25981 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq18293 eq18073
    | exact resolve eq18073 eq18293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18073 eq18293
  have eq25988 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by grind
  clear eq25981
  have eq26005 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq20780 eq25988
    | exact resolve eq25988 eq20780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25988
  have eq26391 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25749 eq689
    | exact resolve eq689 eq25749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq25749
  have eq26416 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq26391
  have eq26436 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26416 eq42
    | exact resolve eq42 eq26416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26437 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26416 eq621
    | (have j0 := eq621 (M.op x y)
       grind)
    | exact resolve eq621 eq26416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26416
  have eq26446 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq26437
    | exact resolve eq26437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26437
  have eq26447 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq26436
    | exact resolve eq26436 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26436
  have eq26450 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26446
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26446
    | exact resolve eq26446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26446
  have eq26451 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26447
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26447
    | exact resolve eq26447 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26447
  have eq26453 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq26450
       have r₂ := eq10077
       grind)
    | exact resolve eq26450 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26450
  have eq26454 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10077 eq26451
    | exact resolve eq26451 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26451
  have eq26456 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq26453
    | exact resolve eq26453 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26453
  have eq26457 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10077 eq26456
    | exact resolve eq26456 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10077 eq26456
  have eq26464 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26454 eq2508
    | exact resolve eq2508 eq26454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508 eq26454
  have eq26481 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq26464
  have eq26489 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20780 eq26481
    | exact resolve eq26481 eq20780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20780 eq26481
  have eq26519 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26457 eq960
    | exact resolve eq960 eq26457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq26457
  have eq26558 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq26519
  have eq26573 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq679 eq26558
    | exact resolve eq26558 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq26558
  have eq26581 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26489 eq26573
    | exact resolve eq26573 eq26489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26489 eq26573
  have eq26582 : y = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq26581
  have eq26589 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq200 y X0
       have i₂ := eq26582
       grind)
    | exact superpose eq26582 eq200
    | exact resolve eq200 eq26582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq26613 : y ≠ y ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq26582
       grind)
    | exact superpose eq26582 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq26582
       grind)
    | exact resolve eq13 eq26582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26619 : x = (M.op y (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq184 x y
       have i₂ := eq26582
       grind)
    | exact superpose eq26582 eq184
    | exact resolve eq184 eq26582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26624 : y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq26613
  have eq27287 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 (M.op X1 (M.op x X2))) (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2829 X0 x X2 x y
       have i₂ := eq26582
       grind)
    | exact superpose eq26582 eq2829
    | exact resolve eq2829 eq26582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28112 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq26624
       grind)
    | exact superpose eq26624 eq36
    | exact resolve eq36 eq26624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26624
  have eq28121 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28112
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28112
    | exact resolve eq28112 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28112
  have eq28171 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 (M.op x x)
       have i₂ := eq26619
       grind)
    | exact superpose eq26619 eq16
    | exact resolve eq16 eq26619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26619
  have eq28472 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq25777
  have eq29779 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq26005 eq142
    | exact resolve eq142 eq26005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq26005
  have eq29814 : x = (k x x) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq30 eq29779
    | exact resolve eq29779 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29779
  have eq29819 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq23853 eq29814
    | exact resolve eq29814 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29814
  have eq30949 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq29819 eq584
    | (have j0 := eq584 (M.op x y)
       grind)
    | (have r₁ := eq584 (M.op x y)
       have r₂ := eq29819
       grind)
    | exact resolve eq584 eq29819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29819
  have eq30951 : (M.op x y) = (k y y) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq30949
  have eq32006 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq30951
       grind)
    | exact superpose eq30951 eq41
    | exact resolve eq41 eq30951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30951
  have eq32016 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq32006
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32006
    | exact resolve eq32006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32006
  have eq32022 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq32016
    | exact resolve eq32016 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32016
  have eq32025 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26582 eq32022
    | exact resolve eq32022 eq26582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32022
  have eq32456 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32025 eq98
    | exact resolve eq98 eq32025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq32025
  have eq32561 : (M.op x y) = (k x x) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq32456
    | exact resolve eq32456 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32456
  have eq32573 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23853 eq32561
    | exact resolve eq32561 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32561
  have eq32581 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq584 (M.op x y)
       grind)
    | (have r₁ := eq32573
       have r₂ := eq584 (M.op x y)
       grind)
    | exact resolve eq32573 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32573
  have eq32614 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op (M.op x y) X1)) (M.op x y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq32581 eq16
    | exact resolve eq16 eq32581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32623 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32581 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq32581
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq32581
       grind)
    | exact resolve eq13 eq32581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32634 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) := by grind
  clear eq32623
  have eq32968 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X2 (M.op X0 (M.op y X1))) (M.op x y)) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq2661 eq32614
    | exact resolve eq32614 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661 eq32614
  have eq39446 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26589 sF0
       have i₂ := eq184 sF0 sF0
       grind)
    | exact superpose eq184 eq26589
    | exact resolve eq26589 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26589
  have eq39486 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39446 eq15639
    | exact resolve eq15639 eq39446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15639
  have eq39511 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39446 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq39446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39446
  have eq39527 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq39486
  have eq39536 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39527 eq189
    | exact resolve eq189 eq39527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39584 : y ≠ (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39527 eq13
    | exact resolve eq13 eq39527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39586 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39527 eq28
    | exact resolve eq28 eq39527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39527
  have eq39613 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq39584
       have r₂ := eq39586
       grind)
    | exact resolve eq39584 eq39586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39584 eq39586
  have eq39615 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39536
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39536
    | exact resolve eq39536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39536
  have eq39762 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39613 eq42
    | exact resolve eq42 eq39613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39613
  have eq39778 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq39762
    | exact resolve eq39762 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39762
  have eq39781 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39778
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39778
    | exact resolve eq39778 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39778
  have eq39784 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39615 eq15696
    | exact resolve eq15696 eq39615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696 eq39615
  have eq39793 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq39784
  have eq39899 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39793 eq184
    | exact resolve eq184 eq39793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39793
  have eq40596 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq39899 eq16
    | exact resolve eq16 eq39899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39899
  have eq41548 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq40596
    | (have j0 := eq40596 (σ x)
       grind)
    | exact resolve eq40596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40596
  have eq41597 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9439 eq41548
    | exact resolve eq41548 eq9439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9439 eq41548
  have eq41602 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41597
       have i₂ := eq28 sF1 sF1
       grind)
    | exact superpose eq28 eq41597
    | (have j1 := eq28 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq41597 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41597
  have eq41641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq39781 eq41602
    | exact resolve eq41602 eq39781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41602
  have eq41642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq41641
    | exact resolve eq41641 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41641
  have eq41643 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq41642
       have r₂ := eq27
       grind)
    | exact resolve eq41642 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41642
  have eq41664 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41643 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq41643
       grind)
    | exact resolve eq13 eq41643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41643
  have eq41677 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq41664
  have eq41684 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39781 eq41677
    | exact resolve eq41677 eq39781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39781 eq41677
  have eq41685 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq41684
  have eq41694 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41685 eq26
    | exact resolve eq26 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41695 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41685 eq32
    | exact resolve eq32 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41714 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41685 eq614
    | exact resolve eq614 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq41940 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26582 eq41714
    | exact resolve eq41714 eq26582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41714
  have eq41955 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq30 eq41695
    | exact resolve eq41695 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41695
  have eq41976 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21710 eq41940
    | exact resolve eq41940 eq21710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21710 eq41940
  have eq41977 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq41976
  have eq41999 : (M.op x y) = (τ (σ y)) ∨ x = y := by
    first
    | exact superpose eq41955 eq29
    | exact resolve eq29 eq41955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42009 : (k (M.op x y) x) = (τ (k (σ y) (σ x))) ∨ x = y := by
    first
    | exact superpose eq41955 eq132
    | exact resolve eq132 eq41955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42041 : (k y x) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq115 eq42009
    | exact resolve eq42009 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42009
  have eq42051 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq41999
    | exact resolve eq41999 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq41999
  have eq43315 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq42051
       grind)
    | exact superpose eq42051 eq18
    | exact resolve eq18 eq42051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43423 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26582
       have i₂ := eq42051
       grind)
    | exact superpose eq42051 eq26582
    | exact resolve eq26582 eq42051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26582
  have eq43447 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq43495 : x = (k (τ (M.op (σ x) (σ y))) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41694 eq278
    | exact resolve eq278 eq41694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq43526 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq41694 eq9287
    | exact resolve eq9287 eq41694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9287 eq41694
  have eq43633 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq43526
  have eq43669 : x = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq43633 eq43495
    | exact resolve eq43495 eq43633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43495 eq43633
  have eq43679 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq43669
    | exact resolve eq43669 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43669
  have eq44604 : x ≠ x ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq584 x
       have i₂ := eq43679
       grind)
    | exact superpose eq43679 eq584
    | (have j0 := eq584 x
       grind)
    | (have r₁ := eq584 x
       have r₂ := eq43679
       grind)
    | exact resolve eq584 eq43679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43679
  have eq44608 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq44604
  have eq46204 : y = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq23910
       have i₂ := eq42041
       grind)
    | exact superpose eq42041 eq23910
    | exact resolve eq23910 eq42041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46210 : x ≠ (k (M.op x y) x) ∨ y = (M.op y x) ∨ (k (M.op x y) x) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq608 y x
       have i₂ := eq42041
       grind)
    | exact superpose eq42041 eq608
    | (have j0 := eq608 (M.op x y) x
       grind)
    | exact resolve eq608 eq42041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq42041
  have eq46213 : x ≠ (k (M.op x y) x) ∨ y = (M.op y x) ∨ y = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq696 eq46210
    | exact resolve eq46210 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq46210
  have eq46217 : y = (k (M.op x y) x) ∨ x = y := by
    first
    | (have r₁ := eq46204
       have r₂ := eq43447
       grind)
    | exact resolve eq46204 eq43447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46204
  have eq46240 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ y = (M.op y x) ∨ y = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq23853 eq46213
    | exact resolve eq46213 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46213
  have eq46244 : (M.op x y) = (k (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq42051 eq46217
    | exact resolve eq46217 eq42051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46217
  have eq46259 : y = (M.op y x) ∨ y = (k (M.op x y) x) ∨ x = y := by
    first
    | (have r₁ := eq46240
       have r₂ := eq32634
       grind)
    | exact resolve eq46240 eq32634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46240
  have eq46266 : y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23853 eq46259
    | exact resolve eq46259 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46259
  have eq46267 : y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23853 eq46266
    | exact resolve eq46266 eq23853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23853 eq46266
  have eq46268 : y = (M.op y x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq46267
       have r₂ := eq28472
       grind)
    | exact resolve eq46267 eq28472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28472 eq46267
  have eq46269 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32634 eq46268
    | exact resolve eq46268 eq32634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32634 eq46268
  have eq46270 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42051 eq46269
    | exact resolve eq46269 eq42051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46269
  have eq47458 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq46244 eq40
    | exact resolve eq40 eq46244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46244
  have eq47465 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq47458
    | exact resolve eq47458 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47458
  have eq47468 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq41955 eq47465
    | exact resolve eq47465 eq41955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41955 eq47465
  have eq47471 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23965 eq47468
    | exact resolve eq47468 eq23965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23965 eq47468
  have eq47542 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq46270
       grind)
    | exact superpose eq46270 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq46270
       grind)
    | exact resolve eq13 eq46270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47555 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq47542
  have eq47614 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47471 eq577
    | exact resolve eq577 eq47471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq47471
  have eq47685 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq621 x
       have i₂ := eq47555
       grind)
    | exact superpose eq47555 eq621
    | (have j0 := eq621 x
       grind)
    | exact resolve eq621 eq47555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47555
  have eq47696 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq47685
  have eq47701 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq47696
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47696
    | exact resolve eq47696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47696
  have eq47893 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq47701 eq16
    | exact resolve eq16 eq47701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53201 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47614 eq47893
    | exact resolve eq47893 eq47614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47893
  have eq53222 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53201
  have eq53307 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53222 eq47614
    | exact resolve eq47614 eq53222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47614 eq53222
  have eq53379 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq53307
  have eq53440 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53379 eq27
    | exact resolve eq27 eq53379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53379
  have eq53666 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq53440
       have r₂ := eq41685
       grind)
    | exact resolve eq53440 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53440
  have eq53668 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53666 eq26
    | exact resolve eq26 eq53666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53945 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47701 eq53668
    | exact resolve eq53668 eq47701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47701 eq53668
  have eq53953 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53945 eq27
    | exact resolve eq27 eq53945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53945
  have eq58018 : ∀ X0 X1 : G, x = (k x (M.op X0 (M.op x X1))) ∨ x = (k x (M.op X0 (M.op x X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq3030 x X1 x
       have i₂ := eq46270
       grind)
    | exact superpose eq46270 eq3030
    | exact resolve eq3030 eq46270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58019 : ∀ X0 X1 : G, x = (k x (M.op X0 (M.op x X1))) ∨ x = (k x (M.op X0 (M.op x X1))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq3030 x X1 x
       have i₂ := eq44608
       grind)
    | exact superpose eq44608 eq3030
    | exact resolve eq3030 eq44608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58030 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op (M.op x y) X1))) ∨ (M.op x y) = (k (M.op x y) (M.op X0 (M.op (M.op x y) X1))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq32581 eq3030
    | exact resolve eq3030 eq32581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58395 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq32581 eq3030
    | exact resolve eq3030 eq32581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030 eq32581
  have eq58722 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq58395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58395
  have eq58759 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op (M.op x y) X1))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq58030 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58030
  have eq58765 : ∀ X0 X1 : G, x = (k x (M.op X0 (M.op x X1))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq58019 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58019
  have eq58766 : ∀ X0 X1 : G, x = (k x (M.op X0 (M.op x X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq58018 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58018
  have eq60668 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op x y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq58722 eq38
    | exact resolve eq38 eq58722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58722
  have eq60685 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op x y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq20 eq60668
    | (have j0 := eq60668 X0
       grind)
    | exact resolve eq60668 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60668
  have eq60689 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op x y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq41977 eq60685
    | exact resolve eq60685 eq41977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60685
  have eq63611 : ∀ X0 : G, x = (k x (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq58766 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58766
    | (have j0 := eq58766 X0 y
       grind)
    | exact resolve eq58766 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64134 : ∀ X0 : G, (τ (σ x)) = (k (τ (σ x)) (M.op X0 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq60689 eq406
    | exact resolve eq406 eq60689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq60689
  have eq64154 : ∀ X0 : G, x = (k x (M.op X0 (M.op x y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq30 eq64134
    | exact resolve eq64134 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64134
  have eq64169 : ∀ X0 : G, x = (k x (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq63611 eq64154
    | (have j0 := eq64154 X0
       have j1 := eq63611 X0
       grind)
    | exact resolve eq64154 eq63611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63611 eq64154
  have eq64226 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq64169 eq36
    | exact resolve eq36 eq64169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64169
  have eq64236 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq64226 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq64226
    | (have j0 := eq64226 X0
       grind)
    | exact resolve eq64226 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64226
  have eq64520 : (σ x) = (k (σ x) (σ (k (M.op x y) y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39511 eq64236
    | exact resolve eq64236 eq39511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39511 eq64236
  have eq64545 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq64520
       have i₂ := eq41 sF0
       grind)
    | exact superpose eq41 eq64520
    | exact resolve eq64520 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq64520
  have eq64558 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq64545
    | exact resolve eq64545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64545
  have eq64568 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43423 eq64558
    | exact resolve eq64558 eq43423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43423 eq64558
  have eq64569 : (σ x) = (k (σ x) (k (σ (M.op x y)) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq64568
  have eq64572 : (σ x) = (k (σ x) (k (σ y) (σ y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41685 eq64569
    | exact resolve eq64569 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64569
  have eq69048 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op (M.op x y) X1)))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq58759 eq38
    | exact resolve eq38 eq58759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq58759
  have eq69062 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op (M.op x y) X1)))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq20 eq69048
    | (have j0 := eq69048 X0 X1
       grind)
    | exact resolve eq69048 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69048
  have eq69071 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ (M.op X0 (M.op (M.op x y) X1)))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq41977 eq69062
    | exact resolve eq69062 eq41977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41977 eq69062
  have eq69687 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op (M.op X0 y) (M.op X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2629 x x (M.op y y)
       have i₂ := eq24043 x
       grind)
    | exact superpose eq24043 eq2629
    | exact resolve eq2629 eq24043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24043
  have eq69688 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op (M.op X0 y) (M.op X0 y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2629 x x (M.op y y)
       have i₂ := eq28171 x
       grind)
    | exact superpose eq28171 eq2629
    | exact resolve eq2629 eq28171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28171
  have eq69933 : ∀ X0 X1 X2 : G, x = (k x (M.op X2 (M.op X0 (M.op (M.op x x) X1)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58765 X2 (M.op (M.op X0 (M.op (M.op x x) X1)) (M.op X0 (M.op (M.op x x) X1)))
       have i₂ := eq2629 x X0 X1
       grind)
    | exact superpose eq2629 eq58765
    | exact resolve eq58765 eq2629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58765
  have eq69934 : ∀ X0 X1 X2 : G, x = (k x (M.op X2 (M.op X0 (M.op (M.op x x) X1)))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58766 X2 (M.op (M.op X0 (M.op (M.op x x) X1)) (M.op X0 (M.op (M.op x x) X1)))
       have i₂ := eq2629 x X0 X1
       grind)
    | exact superpose eq2629 eq58766
    | exact resolve eq58766 eq2629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629 eq58766
  have eq69982 : ∀ X0 X1 X2 : G, x = (k x (M.op X2 (M.op X0 (M.op x X1)))) ∨ y = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq46270 eq69934
    | exact resolve eq69934 eq46270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46270 eq69934
  have eq69983 : ∀ X0 X1 X2 : G, x = (k x (M.op X2 (M.op X0 (M.op x X1)))) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq44608 eq69933
    | exact resolve eq69933 eq44608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44608 eq69933
  have eq70025 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq53666 eq69688
    | exact resolve eq69688 eq53666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69688
  have eq73252 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq69982 (M.op x X0) X0 (M.op x (M.op x (M.op X0 x)))
       have i₂ := eq2829 x X0 x x x
       grind)
    | exact superpose eq2829 eq69982
    | exact resolve eq69982 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69982
  have eq73322 : x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73252 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73252
    | (have j0 := eq73252 y
       grind)
    | exact resolve eq73252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73252
  have eq73400 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73322 eq42
    | exact resolve eq42 eq73322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73322
  have eq73437 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73400
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73400
    | exact resolve eq73400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73400
  have eq74427 : ∀ X0 : G, x = (k x (M.op x X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq69983 (M.op x X0) X0 (M.op x (M.op x (M.op X0 x)))
       have i₂ := eq2829 x X0 x x x
       grind)
    | exact superpose eq2829 eq69983
    | exact resolve eq69983 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69983
  have eq74507 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq74427 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74427
    | (have j0 := eq74427 y
       grind)
    | exact resolve eq74427 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74427
  have eq74592 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq74507 eq42
    | exact resolve eq42 eq74507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq74507
  have eq74622 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq74592
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74592
    | exact resolve eq74592 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74592
  have eq76817 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq221 eq69071
    | exact resolve eq69071 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq69071
  have eq76862 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq76817
    | exact resolve eq76817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76817
  have eq76882 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq73437 eq76862
    | exact resolve eq76862 eq73437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76862
  have eq76910 : (τ (σ x)) = (k (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq76882 eq164
    | exact resolve eq164 eq76882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq76882
  have eq76922 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq30 eq76910
    | exact resolve eq76910 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq76910
  have eq77006 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq76922 eq13
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq76922
       grind)
    | exact resolve eq13 eq76922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77012 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq76922 eq184
    | exact resolve eq184 eq76922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76922
  have eq77026 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq77006
  have eq77054 : x ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq77026
  have eq78479 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq77012 eq16
    | exact resolve eq16 eq77012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77012
  have eq87675 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2995 X0 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq2995
    | exact resolve eq2995 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2995
  have eq87697 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq87675 X0
       have j1 := eq216 X0 X0
       grind)
    | (have r₁ := eq87675 X0
       have r₂ := eq216 X0 X0
       grind)
    | exact resolve eq87675 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq87675
  have eq101338 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq27287 (M.op x (M.op x (M.op X0 x))) (M.op x X0) X0
       have i₂ := eq2829 x X0 x x x
       grind)
    | exact superpose eq2829 eq27287
    | exact resolve eq27287 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27287
  have eq101466 : ∀ X0 : G, (M.op x y) = (M.op (M.op x X0) (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq53666 eq101338
    | exact resolve eq101338 eq53666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101338
  have eq101622 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101466 (M.op x x)
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq101466
    | exact resolve eq101466 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq101466
  have eq108716 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq70025 sF0
       have i₂ := eq184 sF0 sF0
       grind)
    | exact superpose eq184 eq70025
    | exact resolve eq70025 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70025
  have eq108843 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq108716 eq43315
    | exact resolve eq43315 eq108716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43315 eq108716
  have eq108974 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53666 eq108843
    | exact resolve eq108843 eq53666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108843
  have eq109006 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq108974 eq78479
    | exact resolve eq78479 eq108974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78479
  have eq109185 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq109006 X0
       grind)
    | (have r₁ := eq109006 X0
       have r₂ := eq77054
       grind)
    | exact resolve eq109006 eq77054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77054 eq109006
  have eq109208 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15783 eq109185
    | exact resolve eq109185 eq15783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15783 eq109185
  have eq109218 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq108974 eq109208
    | exact resolve eq109208 eq108974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108974 eq109208
  have eq109226 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq584 (M.op x y)
       grind)
    | (have r₁ := eq109218
       have r₂ := eq584 (M.op x y)
       grind)
    | exact resolve eq109218 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq109218
  have eq109233 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109226 eq189
    | exact resolve eq189 eq109226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq109226
  have eq109442 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq109233
    | exact resolve eq109233 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109233
  have eq109454 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41685 eq109442
    | exact resolve eq109442 eq41685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41685 eq109442
  have eq109679 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109454 eq64572
    | exact resolve eq64572 eq109454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64572 eq109454
  have eq109704 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq109679
  have eq109716 : (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28121 eq109704
    | exact resolve eq109704 eq28121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28121 eq109704
  have eq109717 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by grind
  clear eq109716
  have eq154165 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) (M.op x y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq32968 (M.op y X0) X0 (M.op x (M.op x (M.op X0 x)))
       have i₂ := eq2829 x X0 x x y
       grind)
    | exact superpose eq2829 eq32968
    | exact resolve eq32968 eq2829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829 eq32968
  have eq154420 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq154165 (k y y)
       have i₂ := eq551 y
       grind)
    | exact superpose eq551 eq154165
    | (have j1 := eq551 y
       grind)
    | exact resolve eq154165 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq154165
  have eq245722 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69687 y
       have i₂ := eq184 y y
       grind)
    | exact superpose eq184 eq69687
    | exact resolve eq69687 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69687
  have eq245958 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq245722
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq245722
    | exact resolve eq245722 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245722
  have eq245976 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq245958
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq245958
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq245958 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq246060 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq213 y
       have i₂ := eq245958
       grind)
    | exact superpose eq245958 eq213
    | exact resolve eq213 eq245958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq246061 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq214 y
       have i₂ := eq245958
       grind)
    | exact superpose eq245958 eq214
    | exact resolve eq214 eq245958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq246082 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq245958
       grind)
    | exact superpose eq245958 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq245958
       grind)
    | exact resolve eq13 eq245958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246195 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq245958 eq245976
    | exact resolve eq245976 eq245958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245958 eq245976
  have eq246205 : (M.op x y) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq246195
       have r₂ := eq246082
       grind)
    | exact resolve eq246195 eq246082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246082 eq246195
  have eq246573 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq246060 eq37
    | exact resolve eq37 eq246060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq246603 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq246573
    | exact resolve eq246573 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246573
  have eq248100 : (M.op x y) = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9848 y
       have i₂ := eq246205
       grind)
    | exact superpose eq246205 eq9848
    | exact resolve eq9848 eq246205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9848 eq246205
  have eq248130 : (M.op x y) = (k y (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq248100
  have eq248144 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq248130
       have r₂ := eq43447
       grind)
    | exact resolve eq248130 eq43447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43447 eq248130
  have eq248160 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq246060 eq248144
    | exact resolve eq248144 eq246060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246060 eq248144
  have eq248172 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42051 eq248160
    | exact resolve eq248160 eq42051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42051 eq248160
  have eq254155 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53666 eq246603
    | exact resolve eq246603 eq53666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53666
  have eq254157 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12515 eq246603
    | exact resolve eq246603 eq12515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12515 eq246603
  have eq254198 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq254157
  have eq254210 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq74622 eq254198
    | exact resolve eq254198 eq74622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74622 eq254198
  have eq254212 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73437 eq254155
    | exact resolve eq254155 eq73437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254155
  have eq254217 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq254210
       have r₂ := eq8791
       grind)
    | exact resolve eq254210 eq8791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8791 eq254210
  have eq254219 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq254212
       have r₂ := eq53953
       grind)
    | exact resolve eq254212 eq53953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254212
  have eq254235 : (k (M.op x y) x) = (τ (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq254217 eq132
    | exact resolve eq132 eq254217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq254217
  have eq254301 : (k y x) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115 eq254235
    | exact resolve eq254235 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq254235
  have eq254316 : y = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23910 eq254301
    | exact resolve eq254301 eq23910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23910 eq254301
  have eq254320 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq254219 eq254316
    | exact resolve eq254316 eq254219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254316
  have eq254544 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq246061
       have i₂ := eq254219
       grind)
    | exact superpose eq254219 eq246061
    | exact resolve eq246061 eq254219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246061 eq254219
  have eq254547 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq254544
  have eq254784 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq248172 eq36
    | exact resolve eq36 eq248172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq248172
  have eq254837 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq254784
    | exact resolve eq254784 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254784
  have eq254847 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73437 eq254837
    | exact resolve eq254837 eq73437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73437 eq254837
  have eq254852 : y = (M.op x y) := by
    first
    | (have r₁ := eq254847
       have r₂ := eq53953
       grind)
    | exact resolve eq254847 eq53953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53953 eq254847
  have eq254855 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq254852
       grind)
    | exact superpose eq254852 eq18
    | exact resolve eq18 eq254852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq254856 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq254852
       grind)
    | exact superpose eq254852 eq24
    | exact resolve eq24 eq254852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq255051 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq154420
       have i₂ := eq254852
       grind)
    | exact superpose eq254852 eq154420
    | exact resolve eq154420 eq254852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154420 eq254852
  have eq255081 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq255051
  have eq255096 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq254547 eq255081
    | exact resolve eq255081 eq254547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254547 eq255081
  have eq255097 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq255096
  have eq255161 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq254856 eq20
    | exact resolve eq20 eq254856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254856
  have eq255540 : x ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq254855 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq254855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254855
  have eq255624 : (M.op x y) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq255540
       have r₂ := eq254320
       grind)
    | exact resolve eq255540 eq254320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254320 eq255540
  have eq255898 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq255097 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq255097
       grind)
    | exact resolve eq13 eq255097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255097
  have eq255960 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq255898
  have eq256055 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq255624 eq40
    | exact resolve eq40 eq255624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255624
  have eq256078 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq256055
    | exact resolve eq256055 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256055
  have eq256083 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq255161 eq256078
    | exact resolve eq256078 eq255161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256078
  have eq256139 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq255960 eq621
    | (have j0 := eq621 (M.op x y)
       grind)
    | exact resolve eq621 eq255960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq255960
  have eq256164 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq256139
  have eq256172 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq256164
    | exact resolve eq256164 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256164
  have eq256176 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq255161 eq256172
    | exact resolve eq256172 eq255161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256172
  have eq256445 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq256176 eq16
    | exact resolve eq16 eq256176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256176
  have eq282311 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87697 (M.op X0 X0)
       have i₂ := eq184 X0 X0
       grind)
    | exact superpose eq184 eq87697
    | exact resolve eq87697 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq87697
  have eq327754 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq101622 eq22884
    | exact resolve eq22884 eq101622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22884 eq101622
  have eq327977 : (k x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq327754
       have i₂ := eq282311 x
       grind)
    | exact superpose eq282311 eq327754
    | exact resolve eq327754 eq282311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327754
  have eq328153 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq109717 eq327977
    | exact resolve eq327977 eq109717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109717 eq327977
  have eq328252 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq328153
       grind)
    | exact superpose eq328153 eq40
    | exact resolve eq40 eq328153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328264 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x y))) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1255 x x X0
       have i₂ := eq328153
       grind)
    | exact superpose eq328153 eq1255
    | (have j0 := eq1255 x x x
       grind)
    | exact resolve eq1255 eq328153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq328153
  have eq328289 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328264 X0
       have i₂ := eq282311 (σ x)
       grind)
    | exact superpose eq282311 eq328264
    | exact resolve eq328264 eq282311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328264
  have eq328300 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq328252
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq328252
    | exact resolve eq328252 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328252
  have eq328314 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x y))) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328289 X0
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq328289
    | exact resolve eq328289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328289
  have eq328325 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq328300
    | exact resolve eq328300 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328300
  have eq328330 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328314 X0
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq328314
    | exact resolve eq328314 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328314
  have eq328334 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq255161 eq328325
    | exact resolve eq328325 eq255161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328325
  have eq328336 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328330 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq328330
    | (have j0 := eq328330 X0
       grind)
    | exact resolve eq328330 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328330
  have eq328338 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ (M.op x y))) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq328336
    | (have j0 := eq328336 X0
       grind)
    | exact resolve eq328336 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq328336
  have eq328340 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq255161 eq328338
    | exact resolve eq328338 eq255161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328338
  have eq328342 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328340 X0
       have i₂ := eq282311 (σ x)
       grind)
    | exact superpose eq282311 eq328340
    | (have j0 := eq328340 X0
       grind)
    | exact resolve eq328340 eq282311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328340
  have eq328344 : ∀ X0 : G, (σ x) = (σ (k x x)) ∨ (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328342 X0
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq328342
    | (have j0 := eq328342 X0
       grind)
    | exact resolve eq328342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328342
  have eq328347 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328344 X0
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq328344
    | (have j0 := eq328344 X0
       grind)
    | exact resolve eq328344 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq328344
  have eq328348 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq328347 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq328347
    | (have j0 := eq328347 X0
       grind)
    | exact resolve eq328347 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq328347
  have eq328349 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq328334 eq328348
    | (have j0 := eq328348 X0
       grind)
    | exact resolve eq328348 eq328334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328348
  have eq328350 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (M.op X0 (σ y)) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have j0 := eq328349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328349
  have eq328351 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (M.op X0 (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq328334 eq328350
    | exact resolve eq328350 eq328334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328334 eq328350
  have eq328352 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq256445 eq328351
    | exact resolve eq328351 eq256445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256445 eq328351
  have eq328353 : (σ x) = (σ y) := by grind
  clear eq328352
  have eq328354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq328353 eq26
    | exact resolve eq26 eq328353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq328660 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq328353 eq256083
    | exact resolve eq256083 eq328353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256083
  have eq328874 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq328354
       have i₂ := eq282311 sF2
       grind)
    | exact superpose eq282311 eq328354
    | exact resolve eq328354 eq282311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282311 eq328354
  have eq328932 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq328660 eq328874
    | exact resolve eq328874 eq328660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328660 eq328874
  have eq329466 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq328932 eq27
    | exact resolve eq27 eq328932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq328932
  have eq329802 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq255161 eq329466
    | exact resolve eq329466 eq255161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255161 eq329466
  have eq329834 : False := by grind
  exact eq329834

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq33
    | exact resolve eq33 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X2 (M.op X0 X1) X1
       have i₂ := eq24 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq24 eq21
    | exact resolve eq21 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X4 X0 X2
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq72 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq72
    | exact resolve eq72 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq124 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq115 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq144 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq24
    | (have j1 := eq62 X0 X0
       grind)
    | exact resolve eq24 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq164 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq257 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X1 X0 X2
       grind)
    | exact superpose eq21 eq32
    | exact resolve eq32 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq357 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq257 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq257
    | exact resolve eq257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq411 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq357
    | exact resolve eq357 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq357 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq357
    | exact resolve eq357 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X3 X1)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq357 (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X3 X0 X2
       grind)
    | exact superpose eq21 eq357
    | exact resolve eq357 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq411 X0 X1 X2
       have i₂ := eq412 (M.op X0 X2) X1
       grind)
    | exact superpose eq412 eq411
    | exact resolve eq411 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq647 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 X0)
       have i₂ := eq412 X0 X1
       grind)
    | exact superpose eq412 eq22
    | exact resolve eq22 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq435 X1 X0 X0
       grind)
    | exact superpose eq435 eq647
    | exact resolve eq647 eq435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq647
  have eq802 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq110 X1 X0 X1 X0 X2
       have i₂ := eq656 X1 X0
       grind)
    | exact superpose eq656 eq110
    | exact resolve eq110 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq865 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq802 X0 X1 X2
       have i₂ := eq412 X0 X2
       grind)
    | exact superpose eq412 eq802
    | exact resolve eq802 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq1196 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X2 X1 X1
       have i₂ := eq865 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq865 eq21
    | exact resolve eq21 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq865
  have eq1716 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq656 X2 X1
       have i₂ := eq1196 X1 X2 X0
       grind)
    | (have i₁ := eq656 (M.op X2 X0) X0
       have i₂ := eq1196 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1196 eq656
    | exact resolve eq656 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196
  have eq2817 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq144
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq144
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq144 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq2818 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq2817
  have eq9292 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq164 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq164
    | exact resolve eq164 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9308 : ∀ X0 X1 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0
       have i₂ := eq164 X0 X1
       grind)
    | exact superpose eq164 eq124
    | (have j1 := eq164 X0 X1
       grind)
    | exact resolve eq124 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq9400 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9308 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9308
    | (have j0 := eq9308 X0 X1
       grind)
    | exact resolve eq9308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9308
  have eq9412 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9292 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq9292
    | (have j0 := eq9292 X0 X1
       grind)
    | exact resolve eq9292 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9292
  have eq9418 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9412 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9412
    | (have j0 := eq9412 X0 X1
       grind)
    | exact resolve eq9412 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9412
  have eq9479 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 (k X0 X0) X0
       have i₂ := eq9418 X0 (k X0 X0)
       grind)
    | exact superpose eq9418 eq357
    | (have j1 := eq9418 X0 x
       grind)
    | exact resolve eq357 eq9418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9418
  have eq9641 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 (k X0 X0) (k X0 X0)
       have i₂ := eq9479 X0
       grind)
    | exact superpose eq9479 eq24
    | (have j1 := eq9479 X0
       grind)
    | exact resolve eq24 eq9479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9479
  have eq9972 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq9641 (σ X0)
       grind)
    | exact superpose eq9641 eq15
    | (have j1 := eq9641 (σ X0)
       grind)
    | exact resolve eq15 eq9641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9641
  have eq36795 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9400 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9400
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9400 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9400
  have eq36903 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq36795 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36795
  have eq37963 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq2818
       grind)
    | exact superpose eq2818 eq24
    | exact resolve eq24 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq38050 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq37963
  have eq38441 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op (M.op X4 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq106 X3 X1 X4
       have i₂ := eq414 X0 X1 X2 X3
       grind)
    | exact superpose eq414 eq106
    | exact resolve eq106 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq414
  have eq45413 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq36903 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq36903 eq357
    | (have j1 := eq36903 X0 x
       grind)
    | exact resolve eq357 eq36903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36903
  have eq52549 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38441 X0 X1 (M.op X0 X1) X2 X3
       have i₂ := eq656 X1 X0
       grind)
    | exact superpose eq656 eq38441
    | exact resolve eq38441 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq38441
  have eq178329 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq9972
  have eq178624 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178329 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq178329
    | (have j0 := eq178329 X0
       grind)
    | exact resolve eq178329 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178329
  have eq178625 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq178624 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178624
  have eq178701 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq178625 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq178625
    | exact resolve eq178625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178802 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq178625 X0
       grind)
    | exact superpose eq178625 eq124
    | exact resolve eq124 eq178625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq178869 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq178625 X0
       grind)
    | exact superpose eq178625 eq34
    | exact resolve eq34 eq178625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq179229 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq178869 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq178869
    | exact resolve eq178869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178869
  have eq179255 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq178802 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq178802
    | exact resolve eq178802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178802
  have eq179294 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq178701 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq178701
    | exact resolve eq178701 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq178701
  have eq179380 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq179294 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq179294
    | exact resolve eq179294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179294
  have eq183224 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq178625 (k X0 (k X0 X0))
       have i₂ := eq179229 X0
       grind)
    | exact superpose eq179229 eq178625
    | exact resolve eq178625 eq179229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179229
  have eq183232 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq183224 X0
       have i₂ := eq179380 (k X0 (k X0 X0))
       grind)
    | exact superpose eq179380 eq183224
    | exact resolve eq183224 eq179380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183224
  have eq183385 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq183232 X0
       have i₂ := eq179255 X0
       grind)
    | exact superpose eq179255 eq183232
    | exact resolve eq183232 eq179255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179255 eq183232
  have eq188929 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq183385 X0
       grind)
    | exact superpose eq183385 eq24
    | exact resolve eq24 eq183385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq189020 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq357 (σ X0) (σ X0)
       have i₂ := eq183385 X0
       grind)
    | exact superpose eq183385 eq357
    | exact resolve eq357 eq183385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189076 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1716 X0 (σ X0) (σ X0)
       have i₂ := eq183385 X0
       grind)
    | exact superpose eq183385 eq1716
    | exact resolve eq1716 eq183385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq202816 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X2)) = (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq188929 (M.op X1 X2) X3
       have i₂ := eq52549 X1 X2 X1 X0
       grind)
    | (have i₁ := eq188929 (M.op X1 X1) X1
       have i₂ := eq52549 X0 X1 X1 X1
       grind)
    | exact superpose eq52549 eq188929
    | exact resolve eq188929 eq52549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188929
  have eq323483 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq189076 (M.op X2 X1) X1
       have i₂ := eq52549 X2 X1 X2 X3
       grind)
    | (have i₁ := eq189076 (M.op X1 X1) X1
       have i₂ := eq52549 X0 X1 X1 X1
       grind)
    | exact superpose eq52549 eq189076
    | exact resolve eq189076 eq52549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52549 eq189076
  have eq324130 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq323483 X0 X1 X2 x
       have i₂ := eq202816 X0 X1 X2 x
       grind)
    | exact superpose eq202816 eq323483
    | exact resolve eq323483 eq202816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202816 eq323483
  have eq324446 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (k (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324130 X0 X1 X2
       have i₂ := eq178625 (M.op X1 X2)
       grind)
    | exact superpose eq178625 eq324130
    | exact resolve eq324130 eq178625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324130
  have eq324624 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X2) (M.op X1 X2))) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324446 X0 X1 X2
       have i₂ := eq179380 (M.op X1 X2)
       grind)
    | exact superpose eq179380 eq324446
    | exact resolve eq324446 eq179380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324446
  have eq324739 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324624 X0 X1 X2
       have i₂ := eq412 X2 X1
       grind)
    | exact superpose eq412 eq324624
    | exact resolve eq324624 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq324624
  have eq1335585 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq45413 y
       have i₂ := eq38050
       grind)
    | exact superpose eq38050 eq45413
    | exact resolve eq45413 eq38050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38050 eq45413
  have eq1335979 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1335585
  have eq1336361 : (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1335979
       have i₂ := eq178625 x
       grind)
    | exact superpose eq178625 eq1335979
    | exact resolve eq1335979 eq178625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335979
  have eq1336838 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1336361
       have i₂ := eq179380 x
       grind)
    | exact superpose eq179380 eq1336361
    | exact resolve eq1336361 eq179380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336361
  have eq1337308 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq1336838
       have i₂ := eq178625 y
       grind)
    | exact superpose eq178625 eq1336838
    | exact resolve eq1336838 eq178625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336838
  have eq1337777 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1337308
       have i₂ := eq179380 y
       grind)
    | exact superpose eq179380 eq1337308
    | exact resolve eq1337308 eq179380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337308
  have eq1338044 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1337777
       grind)
    | exact superpose eq1337777 eq16
    | exact resolve eq16 eq1337777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337777
  have eq1338047 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1338044
       have r₂ := eq183385 x
       grind)
    | exact resolve eq1338044 eq183385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338044
  have eq1338553 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq183385 (M.op x x)
       have i₂ := eq1338047
       grind)
    | exact superpose eq1338047 eq183385
    | exact resolve eq183385 eq1338047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183385 eq1338047
  have eq1338621 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1338553
       have i₂ := eq324739 x x x
       grind)
    | exact superpose eq324739 eq1338553
    | exact resolve eq1338553 eq324739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324739 eq1338553
  have eq1339095 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1338621
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq1338621
    | exact resolve eq1338621 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1338621
  have eq1339507 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1339095
       have i₂ := eq178625 y
       grind)
    | exact superpose eq178625 eq1339095
    | exact resolve eq1339095 eq178625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178625 eq1339095
  have eq1339733 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1339507
       have i₂ := eq179380 y
       grind)
    | exact superpose eq179380 eq1339507
    | exact resolve eq1339507 eq179380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179380 eq1339507
  have eq1339734 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1339733
  have eq1344414 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189020 y
       have i₂ := eq1339734
       grind)
    | exact superpose eq1339734 eq189020
    | exact resolve eq189020 eq1339734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189020
  have eq1344440 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1339734
       grind)
    | exact superpose eq1339734 eq10
    | exact resolve eq10 eq1339734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339734
  have eq1345356 : x = (M.op y y) := by
    first
    | (have i₁ := eq1344440
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1344440
    | exact resolve eq1344440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344440
  have eq1347048 : x = (M.op x y) := by
    first
    | (have i₁ := eq357 y y
       have i₂ := eq1345356
       grind)
    | exact superpose eq1345356 eq357
    | exact resolve eq357 eq1345356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq1345356
  have eq1378485 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1344414
       grind)
    | exact superpose eq1344414 eq16
    | exact resolve eq16 eq1344414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344414
  have eq1379103 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1378485
       have i₂ := eq1347048
       grind)
    | exact superpose eq1347048 eq1378485
    | exact resolve eq1378485 eq1347048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347048 eq1378485
  have eq1379104 : False := by grind
  exact eq1379104

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq106 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq96
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq122 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq120
  have eq249 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq250 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq249 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq249
    | exact resolve eq249 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq427 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq550 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq551 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq90 X0 X0
       grind)
    | exact superpose eq90 eq54
    | (have j1 := eq90 X0 X0
       grind)
    | exact resolve eq54 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq563 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq551 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq564 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq569 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq564
    | (have j0 := eq564 X0
       grind)
    | exact resolve eq564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq3274 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq427
    | exact resolve eq427 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq427
  have eq3302 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3274
    | (have j0 := eq3274 (σ y) (σ x)
       grind)
    | exact resolve eq3274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3777 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq563 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq563
    | (have j0 := eq563 (τ X0)
       grind)
    | exact resolve eq563 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3797 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3777 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3777
    | (have j0 := eq3777 X0
       grind)
    | exact resolve eq3777 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777
  have eq3809 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3797 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3797
    | (have j0 := eq3797 X0
       grind)
    | exact resolve eq3797 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797
  have eq5912 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq569 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq569
    | exact resolve eq569 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq6015 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5912 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq5912
    | (have j0 := eq5912 X0
       grind)
    | exact resolve eq5912 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5912
  have eq6032 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6015 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6015
    | (have j0 := eq6015 X0
       grind)
    | exact resolve eq6015 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6015
  have eq6045 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6032 X0
       have i₂ := eq39 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq39 eq6032
    | (have j0 := eq6032 X0
       grind)
    | exact resolve eq6032 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq6032
  have eq6054 : ∀ X0 : G, (M.op (k X0 X0) X0) = (k (k X0 (σ (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6045 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq6045
    | (have j0 := eq6045 X0
       grind)
    | exact resolve eq6045 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6045
  have eq6060 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6054 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6054
    | (have j0 := eq6054 X0
       grind)
    | exact resolve eq6054 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6054
  have eq23742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq23743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23742
    | exact resolve eq23742 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23742
  have eq23754 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23743
       have r₂ := eq28
       grind)
    | exact resolve eq23743 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23743
  have eq23770 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23754 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq23754
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23754
       grind)
    | exact resolve eq12 eq23754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23754
  have eq23786 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23770
  have eq23787 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23786
  have eq23803 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23787 eq54
    | exact resolve eq54 eq23787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23787
  have eq23830 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23803
    | exact resolve eq23803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23803
  have eq23837 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23830 eq84
    | exact resolve eq84 eq23830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23830
  have eq23859 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq23837
    | exact resolve eq23837 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23837
  have eq23862 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq23859
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq23859
       have r₂ := eq12 y x
       grind)
    | exact resolve eq23859 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23859
  have eq23864 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq23862
       grind)
    | exact superpose eq23862 eq106
    | exact resolve eq106 eq23862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq23873 : (k y x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  have eq23877 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq250 x
       have i₂ := eq23862
       grind)
    | exact superpose eq23862 eq250
    | exact resolve eq250 eq23862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq23862
  have eq23903 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq23864
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23864
    | exact resolve eq23864 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23864
  have eq25290 : x ≠ (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq23873
  have eq25321 : x ≠ y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq25290
       have i₂ := eq23877
       grind)
    | exact superpose eq23877 eq25290
    | exact resolve eq25290 eq23877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23877 eq25290
  have eq25322 : x ≠ y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq25321
  have eq28028 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have r₁ := eq23903
       have r₂ := eq25322
       grind)
    | exact resolve eq23903 eq25322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23903 eq25322
  have eq28047 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq28028 eq3809
    | (have j0 := eq3809 (σ x)
       grind)
    | exact resolve eq3809 eq28028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3809
  have eq28062 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq27 eq28047
    | exact resolve eq28047 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28047
  have eq28063 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq28062
  have eq28143 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq28063
  have eq28731 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq28143 eq28028
    | exact resolve eq28028 eq28143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28028 eq28143
  have eq28748 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq28731
  have eq28772 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq28748 eq54
    | exact resolve eq54 eq28748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28748
  have eq28806 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq27 eq28772
    | exact resolve eq28772 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28772
  have eq28807 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28806
  have eq28812 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq28807
       grind)
    | exact superpose eq28807 eq77
    | exact resolve eq77 eq28807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq28807
  have eq28841 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28812
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28812
    | exact resolve eq28812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28812
  have eq28873 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28841 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq28841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28841
  have eq28876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28873
    | exact resolve eq28873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28873
  have eq28877 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq28876
  have eq29653 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28877 eq3274
    | exact resolve eq3274 eq28877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3274
  have eq36442 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29653 eq28877
    | exact resolve eq28877 eq29653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28877 eq29653
  have eq36487 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36442
  have eq36815 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36487 eq54
    | exact resolve eq54 eq36487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq36487
  have eq36854 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq36815
    | exact resolve eq36815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36815
  have eq36855 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq36854
  have eq36858 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq36855 eq28
    | exact resolve eq28 eq36855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq36868 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq36855 eq3302
    | exact resolve eq3302 eq36855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3302
  have eq36916 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq36868
    | exact resolve eq36868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36868
  have eq36918 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq36855 eq36916
    | exact resolve eq36916 eq36855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36916
  have eq36920 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36918 eq122
    | exact resolve eq122 eq36918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq36942 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  have eq36948 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq36918 eq255
    | exact resolve eq255 eq36918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36986 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq36942
    | exact resolve eq36942 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq36942
  have eq36996 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq36920
    | exact resolve eq36920 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36920
  have eq36998 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq36855 eq36986
    | exact resolve eq36986 eq36855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36855 eq36986
  have eq37376 : (τ (σ y)) = (k y x) := by
    first
    | exact superpose eq36948 eq84
    | exact resolve eq84 eq36948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq36948
  have eq37432 : y = (k y x) := by
    first
    | exact superpose eq30 eq37376
    | exact resolve eq37376 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37376
  have eq38179 : (τ (σ x)) = (k x y) := by
    first
    | exact superpose eq36998 eq60
    | exact resolve eq60 eq36998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq36998
  have eq38198 : x = (k x y) := by
    first
    | exact superpose eq29 eq38179
    | exact resolve eq38179 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38179
  have eq44096 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6060 y
       have i₂ := eq36996
       grind)
    | exact superpose eq36996 eq6060
    | (have j0 := eq6060 y
       grind)
    | exact resolve eq6060 eq36996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6060 eq36996
  have eq44112 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44096
       have i₂ := eq38198
       grind)
    | exact superpose eq38198 eq44096
    | exact resolve eq44096 eq38198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38198 eq44096
  have eq44129 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq44112
    | exact resolve eq44112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44112
  have eq60015 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq255 y
       have i₂ := eq44129
       grind)
    | exact superpose eq44129 eq255
    | exact resolve eq255 eq44129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq44129
  have eq61237 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq563 y
       have i₂ := eq60015
       grind)
    | exact superpose eq60015 eq563
    | (have j0 := eq563 y
       grind)
    | exact resolve eq563 eq60015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq60015
  have eq61254 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq61237
  have eq61265 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61254
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq61254
    | exact resolve eq61254 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq61254
  have eq61279 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36918 eq61265
    | exact resolve eq61265 eq36918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36918 eq61265
  have eq61280 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq61279
  have eq61292 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq61280 eq30
    | exact resolve eq30 eq61280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq61280
  have eq61596 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq61292
    | exact resolve eq61292 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61292
  have eq62029 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq61596 eq21
    | exact resolve eq21 eq61596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61596
  have eq62300 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq62029
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62029
    | exact resolve eq62029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62029
  have eq62323 : x = y := by
    first
    | (have r₁ := eq62300
       have r₂ := eq36858
       grind)
    | exact resolve eq62300 eq36858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62300
  have eq62336 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq62323
       grind)
    | exact superpose eq62323 eq19
    | exact resolve eq19 eq62323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq62540 : x = (k x x) := by
    first
    | (have i₁ := eq37432
       have i₂ := eq62323
       grind)
    | exact superpose eq62323 eq37432
    | exact resolve eq37432 eq62323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37432 eq62323
  have eq63680 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq62540
       grind)
    | exact superpose eq62540 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq62540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62540
  have eq63681 : x = (M.op x x) := by grind
  clear eq63680
  have eq63692 : x = (M.op x y) := by
    first
    | (have i₁ := eq63681
       have i₂ := eq62336
       grind)
    | exact superpose eq62336 eq63681
    | exact resolve eq63681 eq62336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62336 eq63681
  have eq63729 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq63692 eq21
    | exact resolve eq21 eq63692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq63692
  have eq64042 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq63729
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq63729
    | exact resolve eq63729 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq63729
  have eq64108 : False := by grind
  exact eq64108

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq427 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq576 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq3390 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq427
    | exact resolve eq427 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq427
  have eq3416 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3390 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3390
    | (have j0 := eq3390 y x
       grind)
    | exact resolve eq3390 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3418 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3390
    | (have j0 := eq3390 (σ y) (σ x)
       grind)
    | exact resolve eq3390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12110 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12110
    | exact resolve eq12110 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12110
  have eq12122 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12111
       have r₂ := eq28
       grind)
    | exact resolve eq12111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12111
  have eq12124 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12122
    | exact resolve eq12122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12122
  have eq12150 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12124 eq3390
    | exact resolve eq3390 eq12124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12124
  have eq12151 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12150
    | exact resolve eq12150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq12152 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12151
  have eq12181 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3390 y y
       have i₂ := eq12152
       grind)
    | exact superpose eq12152 eq3390
    | exact resolve eq3390 eq12152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12152
  have eq12182 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12181
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12181
    | exact resolve eq12181 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12183 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12182
  have eq12188 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12183 eq28
    | exact resolve eq28 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12197 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12183 eq3418
    | exact resolve eq3418 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418
  have eq12205 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12197
    | exact resolve eq12197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12197
  have eq12329 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12205
  have eq12507 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12183 eq12329
    | exact resolve eq12329 eq12183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12183 eq12329
  have eq12519 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12507
  have eq13000 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12519 eq87
    | exact resolve eq87 eq12519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq12519
  have eq13016 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq13000
  have eq13026 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13016
       have r₂ := eq12188
       grind)
    | exact resolve eq13016 eq12188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12188 eq13016
  have eq13488 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3390 y y
       have i₂ := eq13026
       grind)
    | exact superpose eq13026 eq3390
    | exact resolve eq3390 eq13026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026
  have eq13489 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13488
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13488
    | exact resolve eq13488 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13488
  have eq13490 : x = (M.op x y) := by grind
  clear eq13489
  have eq13496 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13490 eq21
    | exact resolve eq21 eq13490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq13554 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq13490 eq3416
    | exact resolve eq3416 eq13490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq13562 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq13554
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13554
    | exact resolve eq13554 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq13554
  have eq13612 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13496
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13496
    | exact resolve eq13496 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13496
  have eq13613 : x = (M.op y y) := by
    first
    | exact superpose eq13490 eq13562
    | exact resolve eq13562 eq13490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13490 eq13562
  have eq13615 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13612 eq27
    | exact resolve eq27 eq13612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13752 : x = (k x y) := by grind
  clear eq13613
  have eq14043 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq576 x y
       have i₂ := eq13752
       grind)
    | exact superpose eq13752 eq576
    | (have j0 := eq576 x y
       grind)
    | exact resolve eq576 eq13752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq13752
  have eq14048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq14043
  have eq14051 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14048
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14048
    | exact resolve eq14048 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14048
  have eq14061 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14051
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14051
    | exact resolve eq14051 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14051
  have eq14071 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq14061
    | exact resolve eq14061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14061
  have eq14079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq13612 eq14071
    | exact resolve eq14071 eq13612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14071
  have eq14082 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq14079
       have r₂ := eq28
       grind)
    | exact resolve eq14079 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14079
  have eq14085 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14082
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14082
    | exact resolve eq14082 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq14082
  have eq14087 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq14085
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14085
    | exact resolve eq14085 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14085
  have eq14089 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq13612 eq14087
    | exact resolve eq14087 eq13612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13612 eq14087
  have eq14632 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14089 eq3390
    | exact resolve eq3390 eq14089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390 eq14089
  have eq14633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13615 eq14632
    | exact resolve eq14632 eq13615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13615 eq14632
  have eq14636 : False := by grind
  exact eq14636
