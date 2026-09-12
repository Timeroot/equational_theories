import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation437`: `x = x ◇ (y ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation437 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law437 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law437.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
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
  have eq559 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
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
  have eq564 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq559
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq559
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq1210 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
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
  have eq1218 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1210
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1219 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1218
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1218
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1218
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1218
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1218
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1218 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1218
  have eq1221 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1219
  have eq1297 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1221
       grind)
    | exact superpose eq1221 eq9
    | exact resolve eq9 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1298 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1297
  have eq1299 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1298
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1298
    | exact resolve eq1298 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1300 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1299
  have eq1301 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1300
  have eq1379 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1301
       grind)
    | exact superpose eq1301 eq10
    | exact resolve eq10 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1381 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1379
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1379
    | exact resolve eq1379 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1382 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1381
  have eq1385 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1382
       grind)
    | exact superpose eq1382 eq22
    | exact resolve eq22 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1432 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1385
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1385
    | exact resolve eq1385 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1385
  have eq1454 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq564
       have i₂ := eq1432
       grind)
    | exact superpose eq1432 eq564
    | (have r₁ := eq564
       have r₂ := eq1432
       grind)
    | exact resolve eq564 eq1432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq1432
  have eq1457 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1454
  have eq1461 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1457
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1457
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1457
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1457
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1457
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1457 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1457
  have eq1462 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1461
  have eq1463 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1462
  have eq1465 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1463
       have r₂ := eq1382
       grind)
    | exact resolve eq1463 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382 eq1463
  have eq1466 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1465
       grind)
    | exact superpose eq1465 eq9
    | exact resolve eq9 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1467 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1466
  have eq1468 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1467
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1467
    | exact resolve eq1467 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1469 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1468
  have eq1470 : (σ x) = (σ y) := by grind
  clear eq1469
  have eq1472 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1470
       grind)
    | exact superpose eq1470 eq15
    | exact resolve eq15 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1519 : x = y := by
    first
    | (have i₁ := eq1472
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1472
    | exact resolve eq1472 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1522 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1519
       grind)
    | exact superpose eq1519 eq9
    | exact resolve eq9 eq1519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1523 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1522
  have eq1524 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1523
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1523
    | exact resolve eq1523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1523
  have eq1525 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1524
  have eq1526 : False := by grind
  exact eq1526

/-- `Equation4400`: `x ◇ (x ◇ y) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_x_pxy_pyx_Equation4400 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4400 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4400.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) X2) := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X3) = (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) x x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) X0) := by
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
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 (M.op X0 X1))
       have r₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 X0 X1 X3
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq189 : ∀ X1 : G, (M.op (M.op x (M.op x y)) X1) = (M.op (M.op x y) (M.op x (M.op x y))) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X1) := by
    intro X1
    first
    | exact superpose eq180 eq189
    | exact resolve eq189 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq193 : (M.op x (M.op x y)) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq191 x
       have i₂ := eq16 x sF0 x
       grind)
    | exact superpose eq16 eq191
    | exact resolve eq191 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq213 : (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ x = (k x (M.op x (M.op x y))) := by
    first
    | exact superpose eq193 eq13
    | (have j0 := eq13 x (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 x (M.op x (M.op x y))
       have r₂ := eq193
       grind)
    | exact resolve eq13 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : x = (k x (M.op x (M.op x y))) := by grind
  clear eq213
  have eq216 : (σ x) = (k (σ x) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq214 eq35
    | exact resolve eq35 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq214
  have eq217 : (σ x) = (k (σ x) (σ (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq216
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq216
    | exact resolve eq216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq490 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq498 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x (M.op x (M.op x y))) ∨ x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq193
       have i₂ := eq11 (M.op x sF0) x
       grind)
    | exact superpose eq11 eq193
    | (have j1 := eq11 (M.op x (M.op x y)) x
       grind)
    | exact resolve eq193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq531 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have j1 := eq184 x (M.op x y) x
       grind)
    | (have r₁ := eq513
       have r₂ := eq184 x y (k (M.op x (M.op x y)) x)
       grind)
    | (have r₁ := eq513
       have r₂ := eq184 x (M.op x y) x
       grind)
    | exact resolve eq513 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq513
  have eq562 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) := by
    first
    | (have j1 := eq13 (M.op x (M.op x y)) x
       grind)
    | (have r₁ := eq546
       have r₂ := eq13 (M.op x (M.op x y)) x
       grind)
    | exact resolve eq546 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq570 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq589 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq583 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq583 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq583 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq583 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq609 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (M.op (M.op x y) X0) x) := by
    intro X0
    first
    | exact superpose eq180 eq562
    | exact resolve eq562 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq616 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (k (σ (M.op (M.op x y) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq609 eq39
    | exact resolve eq39 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq979 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) x
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1013 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq490
       grind)
    | exact superpose eq490 eq39
    | exact resolve eq39 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1014 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1013
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1013
    | exact resolve eq1013 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1016 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1014
    | exact resolve eq1014 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1170 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ (M.op X0 (M.op X0 X1)) ∨ (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have i₂ := eq979 X0 X1
       grind)
    | exact superpose eq979 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X0 X1))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X0 X1))
       have r₂ := eq979 X0 X1
       grind)
    | exact resolve eq13 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq1199 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1256 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op y (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op y (M.op y X0))
       have i₂ := eq1199 y X0
       grind)
    | exact superpose eq1199 eq36
    | exact resolve eq36 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1260 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op sF3 (M.op sF3 x))
       have i₂ := eq1199 sF3 x
       grind)
    | exact superpose eq1199 eq107
    | exact resolve eq107 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1199
  have eq1261 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq31 eq1260
    | exact resolve eq1260 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1260
  have eq1265 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op y (M.op y X0)))) := by
    intro X0
    first
    | (have i₁ := eq1256 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1256
    | (have j0 := eq1256 X0
       grind)
    | exact resolve eq1256 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq2161 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1016 eq498
    | exact resolve eq498 eq1016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq1016
  have eq2170 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2161
       have r₂ := eq27
       grind)
    | exact resolve eq2161 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2175 : y = (k y (τ (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2170 eq1261
    | exact resolve eq1261 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq2200 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2170 eq2175
    | exact resolve eq2175 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2205 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq2200
    | exact resolve eq2200 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2207 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq2205
       have r₂ := eq13 y x
       grind)
    | exact resolve eq2205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2209 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq490
       have i₂ := eq2207
       grind)
    | exact superpose eq2207 eq490
    | exact resolve eq490 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490 eq2207
  have eq2213 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2209
  have eq2244 : ∀ X0 : G, (M.op y x) = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y x x
       have i₂ := eq2213
       grind)
    | exact superpose eq2213 eq16
    | exact resolve eq16 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2262 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2213 eq2244
    | exact resolve eq2244 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213 eq2244
  have eq2356 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2262 y
       grind)
    | exact superpose eq2262 eq18
    | (have j1 := eq2262 y
       grind)
    | exact resolve eq18 eq2262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq2383 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2356
  have eq2395 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2383 eq181
    | exact resolve eq181 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2395 eq26
    | (have j1 := eq2395 (σ y)
       grind)
    | exact resolve eq26 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2395
  have eq2459 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2383 eq2414
    | exact resolve eq2414 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq2465 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2459 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2459
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2459
       grind)
    | exact resolve eq13 eq2459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2476 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2465
  have eq2486 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2476 eq141
    | exact resolve eq141 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2476
  have eq2492 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2486
    | exact resolve eq2486 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2548 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq531 x x
       have i₂ := eq2492
       grind)
    | exact superpose eq2492 eq531
    | (have j0 := eq531 x x
       grind)
    | (have r₁ := eq531 x x
       have r₂ := eq2492
       grind)
    | exact resolve eq531 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq2549 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2548
  have eq2550 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2549
  have eq2558 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x x x
       have i₂ := eq2550
       grind)
    | exact superpose eq2550 eq176
    | exact resolve eq176 eq2550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2857 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2550
       have i₂ := eq2558 x X0
       grind)
    | (have i₁ := eq2550
       have i₂ := eq2558 X0 x
       grind)
    | exact superpose eq2558 eq2550
    | exact resolve eq2550 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2858 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq2558 y X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq2558 X0 y
       grind)
    | exact superpose eq2558 eq18
    | (have j1 := eq2558 y X0
       grind)
    | exact resolve eq18 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2886 : ∀ X0 : G, x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2899 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2858 eq2886
    | (have j0 := eq2886 y
       grind)
    | exact resolve eq2886 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858 eq2886
  have eq2900 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2899
  have eq2910 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2900
       grind)
    | exact superpose eq2900 eq18
    | exact resolve eq18 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2911 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2900
       grind)
    | exact superpose eq2900 eq24
    | exact resolve eq24 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2917 : ∀ X0 : G, (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op (M.op x y) X0)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1265 X0
       have i₂ := eq2900
       grind)
    | exact superpose eq2900 eq1265
    | exact resolve eq1265 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265 eq2900
  have eq2926 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq180 eq2917
    | exact resolve eq2917 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917
  have eq2930 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2911
    | exact resolve eq2911 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2911
  have eq2931 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2910 eq2926
    | exact resolve eq2926 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq2932 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2931
    | exact resolve eq2931 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq2933 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2930 eq2932
    | exact resolve eq2932 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq2969 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2910 eq180
    | exact resolve eq180 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq2973 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2910 eq217
    | exact resolve eq217 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq3012 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2973
    | exact resolve eq2973 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973
  have eq3017 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2930 eq3012
    | exact resolve eq3012 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930 eq3012
  have eq3039 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2933 eq531
    | (have j0 := eq531 (σ y) (σ y)
       grind)
    | (have r₁ := eq531 (σ y) (σ y)
       have r₂ := eq2933
       grind)
    | exact resolve eq531 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq3040 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3039
  have eq3041 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3040
  have eq3140 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3041 eq176
    | exact resolve eq176 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3202 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3140 eq3041
    | exact resolve eq3041 eq3140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041 eq3140
  have eq3221 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3202
  have eq3270 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3221 eq2170
    | exact resolve eq2170 eq3221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170 eq3221
  have eq3289 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq3270
  have eq3300 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2383 eq3289
    | exact resolve eq3289 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383 eq3289
  have eq3304 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2969 eq3300
    | exact resolve eq3300 eq2969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969 eq3300
  have eq3305 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3304
  have eq3653 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3017 eq589
    | (have j0 := eq589 (σ x) (σ y)
       grind)
    | exact resolve eq589 eq3017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq3017
  have eq3677 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3653
    | exact resolve eq3653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3653
  have eq3686 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3677
    | exact resolve eq3677 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq3693 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3686
       have r₂ := eq3305
       grind)
    | exact resolve eq3686 eq3305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3686
  have eq3697 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3305 eq3693
    | exact resolve eq3693 eq3305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305 eq3693
  have eq3698 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3697
  have eq3704 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3698 eq181
    | exact resolve eq181 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq3740 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3704 eq26
    | (have j1 := eq3704 (σ y)
       grind)
    | exact resolve eq26 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3816 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3698 eq3740
    | exact resolve eq3740 eq3698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698 eq3740
  have eq3830 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3816 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq3816
       grind)
    | exact resolve eq13 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq3843 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3830
  have eq3861 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3843 eq141
    | exact resolve eq141 eq3843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq3843
  have eq3870 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3861
    | exact resolve eq3861 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3861
  have eq3949 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq531 x x
       have i₂ := eq3870
       grind)
    | exact superpose eq3870 eq531
    | (have j0 := eq531 x x
       grind)
    | (have r₁ := eq531 x x
       have r₂ := eq3870
       grind)
    | exact resolve eq531 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870
  have eq3950 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3949
  have eq3951 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq3950
  have eq3967 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x x x x
       have i₂ := eq3951
       grind)
    | exact superpose eq3951 eq176
    | exact resolve eq176 eq3951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4328 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3951
       have i₂ := eq3967 x X0
       grind)
    | (have i₁ := eq3951
       have i₂ := eq3967 X0 x
       grind)
    | exact superpose eq3967 eq3951
    | exact resolve eq3951 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951
  have eq4340 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2910
       have i₂ := eq3967 sF0 x
       grind)
    | (have i₁ := eq2910
       have i₂ := eq3967 X0 sF0
       grind)
    | exact superpose eq3967 eq2910
    | (have j1 := eq3967 y X0
       grind)
    | exact resolve eq2910 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910 eq3967
  have eq4361 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4340 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4340
  have eq4363 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328
  have eq4400 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4361 eq4363
    | (have j0 := eq4363 y
       grind)
    | exact resolve eq4363 eq4361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4361 eq4363
  have eq4401 : x = (M.op x y) := by grind
  clear eq4400
  have eq4428 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4401
       grind)
    | exact superpose eq4401 eq18
    | exact resolve eq18 eq4401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4429 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4401
       grind)
    | exact superpose eq4401 eq22
    | exact resolve eq22 eq4401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4401
  have eq4454 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4429 eq20
    | exact resolve eq20 eq4429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4429
  have eq4542 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq4428 eq616
    | exact resolve eq616 eq4428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq4428
  have eq4565 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq4542
    | exact resolve eq4542 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4542
  have eq4573 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4454 eq4565
    | exact resolve eq4565 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4655 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4573 eq531
    | (have j0 := eq531 (σ x) (σ x)
       grind)
    | (have r₁ := eq531 (σ x) (σ x)
       have r₂ := eq4573
       grind)
    | exact resolve eq531 eq4573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq4573
  have eq4656 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4655
  have eq4657 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4656
  have eq4688 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq4657 eq176
    | exact resolve eq176 eq4657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4815 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq4688 eq4657
    | exact resolve eq4657 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657 eq4688
  have eq4889 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4815 eq26
    | (have j1 := eq4815 (σ y)
       grind)
    | exact resolve eq26 eq4815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4815
  have eq4932 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq4889 eq27
    | exact resolve eq27 eq4889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq4889
  have eq4948 : False := by grind
  exact eq4948

/-- `Equation4401`: `x ◇ (x ◇ y) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pxx_pxy_pyx_Equation4401 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4401 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4401.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X2) X0) := by
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
  have eq174 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op (M.op x y) x) := by
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
  have eq180 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : y ≠ (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  have eq186 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op (M.op x y) x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq179 (M.op x x)
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq217 : (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op x x) = (k x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq187 eq13
    | (have j0 := eq13 x (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq13 x (M.op (M.op x y) x)
       have r₂ := eq187
       grind)
    | exact resolve eq13 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq220 : (M.op x x) = (k x (M.op (M.op x y) x)) := by grind
  clear eq217
  have eq350 : (k (σ x) (σ (M.op (M.op x y) x))) = (σ (M.op x x)) := by
    first
    | exact superpose eq220 eq35
    | exact resolve eq35 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq220
  have eq821 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq824 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq186
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq186
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq200
       have i₂ := eq11 sF2 sF4
       grind)
    | exact superpose eq11 eq200
    | (have j1 := eq11 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have j1 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq864
       have r₂ := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq864
       have r₂ := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq864 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq879 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq850
       have r₂ := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq850
       have r₂ := eq12 x (M.op x y)
       grind)
    | exact resolve eq850 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq950 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1506 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op X0 X2) X0)
       have i₂ := eq174 X0 X2 X1
       grind)
    | exact superpose eq174 eq13
    | (have j0 := eq13 X0 (M.op (M.op X0 X2) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 x) X0)
       have r₂ := eq174 X0 x x
       grind)
    | exact resolve eq13 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1537 : ∀ X0 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X0 X2) X0)) := by
    intro X0 X2
    first
    | (have j0 := eq1506 X0 x X2
       grind)
    | (have r₁ := eq1506 X0 x x
       have r₂ := eq176 X0 x x
       grind)
    | (have r₁ := eq1506 X0 x x
       have r₂ := eq176 X0 x x
       grind)
    | exact resolve eq1506 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1957 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq821
       grind)
    | exact superpose eq821 eq39
    | exact resolve eq39 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq1958 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1957
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1957
    | exact resolve eq1957 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1957
  have eq1960 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq1958
    | exact resolve eq1958 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq2343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1960 eq824
    | exact resolve eq824 eq1960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2350 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2343
       have r₂ := eq27
       grind)
    | exact resolve eq2343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq2355 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2350 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2350
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2350
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2350
       grind)
    | exact resolve eq12 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2357 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2350 eq16
    | exact resolve eq16 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2363 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2350 eq181
    | exact resolve eq181 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2369 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq2355
  have eq2374 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq2350 eq2363
    | exact resolve eq2363 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350 eq2363
  have eq2380 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq2357
    | (have j0 := eq2357 X0
       grind)
    | exact resolve eq2357 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2357
  have eq2382 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq2369
    | exact resolve eq2369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2383 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq2382
  have eq2387 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2374 eq2380
    | exact resolve eq2380 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374 eq2380
  have eq2388 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq2383
    | exact resolve eq2383 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2389 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2387 eq2388
    | exact resolve eq2388 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2411 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176 y X0 x
       have i₂ := eq2387
       grind)
    | exact superpose eq2387 eq176
    | exact resolve eq176 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2414 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 y X0 x
       have i₂ := eq2387
       grind)
    | exact superpose eq2387 eq181
    | exact resolve eq181 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2425 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2387 eq2414
    | exact resolve eq2414 eq2387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387 eq2414
  have eq2428 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2411 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2411
    | (have j0 := eq2411 X0
       grind)
    | exact resolve eq2411 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2411
  have eq2603 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2389 eq152
    | exact resolve eq152 eq2389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2608 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq2603
    | exact resolve eq2603 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2713 : ∀ X1 : G, x = (M.op (M.op y X1) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq2425 x
       grind)
    | exact superpose eq2425 eq16
    | exact resolve eq16 eq2425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq2758 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2428 eq2713
    | exact resolve eq2713 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428 eq2713
  have eq2804 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2758 eq200
    | exact resolve eq200 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2818 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq2831 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2804
    | exact resolve eq2804 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2804
  have eq2840 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2758 eq2831
    | exact resolve eq2831 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq3198 : x ≠ x ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq865 y x
       have i₂ := eq2608
       grind)
    | exact superpose eq2608 eq865
    | (have j0 := eq865 y x
       grind)
    | (have r₁ := eq865 y x
       have r₂ := eq2608
       grind)
    | exact resolve eq865 eq2608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq3199 : x ≠ x ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3198
  have eq3200 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3199
  have eq3203 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3200
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3200
    | exact resolve eq3200 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200
  have eq3204 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3203
  have eq3211 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3204
       grind)
    | exact superpose eq3204 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3204
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3204
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3204
       grind)
    | exact resolve eq12 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3216 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq176 y X0 x
       have i₂ := eq3204
       grind)
    | exact superpose eq3204 eq176
    | exact resolve eq176 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3219 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 y X0 x
       have i₂ := eq3204
       grind)
    | exact superpose eq3204 eq181
    | exact resolve eq181 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3225 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3211
  have eq3233 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3204 eq3219
    | exact resolve eq3219 eq3204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3204 eq3219
  have eq3236 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3216 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3216
    | (have j0 := eq3216 X0
       grind)
    | exact resolve eq3216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216
  have eq3240 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3225
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3225
    | exact resolve eq3225 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225
  have eq3241 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3240
  have eq3245 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3241
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3241
    | exact resolve eq3241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241
  have eq3280 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3245
       grind)
    | exact superpose eq3245 eq40
    | exact resolve eq40 eq3245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3245
  have eq3284 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3280
    | exact resolve eq3280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3286 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3284
    | exact resolve eq3284 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq3338 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3286 eq865
    | (have j0 := eq865 (σ y) (σ x)
       grind)
    | exact resolve eq865 eq3286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3341 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3338
    | exact resolve eq3338 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3342 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3341
  have eq3348 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2758 eq950
    | (have r₁ := eq950
       have r₂ := eq2758
       grind)
    | exact resolve eq950 eq2758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq3349 : (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3348
  have eq3350 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2840 eq3349
    | exact resolve eq3349 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq3351 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3350
       have r₂ := eq2818
       grind)
    | exact resolve eq3350 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3352 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2840 eq3351
    | exact resolve eq3351 eq2840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2840 eq3351
  have eq3518 : ∀ X1 : G, x = (M.op (M.op y X1) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq3233 x
       grind)
    | exact superpose eq3233 eq16
    | exact resolve eq16 eq3233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq3575 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3236 eq3518
    | exact resolve eq3518 eq3236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3236 eq3518
  have eq3620 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3575 eq27
    | exact resolve eq27 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3622 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3575 eq200
    | exact resolve eq200 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3650 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3622
    | exact resolve eq3622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3622
  have eq3660 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3575 eq3650
    | exact resolve eq3650 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650
  have eq5945 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3352 eq1960
    | exact resolve eq1960 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5949 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3352 eq141
    | exact resolve eq141 eq3352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq5955 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5945
  have eq5960 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq5949
    | exact resolve eq5949 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5949
  have eq5963 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5955
       have r₂ := eq3620
       grind)
    | exact resolve eq5955 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620 eq5955
  have eq5965 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3575 eq5960
    | exact resolve eq5960 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5960
  have eq5968 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3575 eq5963
    | exact resolve eq5963 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5963
  have eq6470 : x ≠ x ∨ (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq5968
       grind)
    | exact superpose eq5968 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5968
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5968
       grind)
    | exact resolve eq13 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6475 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 y X0 x
       have i₂ := eq5968
       grind)
    | exact superpose eq5968 eq176
    | exact resolve eq176 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6480 : ∀ X0 : G, (M.op y x) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq181 y X0 x
       have i₂ := eq5968
       grind)
    | exact superpose eq5968 eq181
    | exact resolve eq181 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6484 : (M.op y y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1537 y x
       have i₂ := eq5968
       grind)
    | exact superpose eq5968 eq1537
    | exact resolve eq1537 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq6486 : (k y x) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6470
  have eq6496 : (k y (M.op x y)) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6484
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6484
    | exact resolve eq6484 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6484
  have eq6500 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq5968 eq6480
    | exact resolve eq6480 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5968 eq6480
  have eq6505 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6475 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6475
    | (have j0 := eq6475 X0
       grind)
    | exact resolve eq6475 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6475
  have eq6510 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5965 eq6486
    | exact resolve eq6486 eq5965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5965 eq6486
  have eq6672 : ∀ X0 : G, (M.op y y) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq176 y X0 y
       have i₂ := eq6510
       grind)
    | exact superpose eq6510 eq176
    | exact resolve eq176 eq6510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq6677 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq181 y X0 y
       have i₂ := eq6510
       grind)
    | exact superpose eq6510 eq181
    | exact resolve eq181 eq6510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6510
  have eq6704 : ∀ X0 : G, (k y (M.op x y)) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq6496 eq6677
    | exact resolve eq6677 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6677
  have eq6707 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq6496 eq6672
    | exact resolve eq6672 eq6496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6496 eq6672
  have eq6710 : x = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6500 eq6704
    | exact resolve eq6704 eq6500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6500 eq6704
  have eq6713 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6505 eq6707
    | exact resolve eq6707 eq6505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505 eq6707
  have eq6894 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6713 eq6710
    | exact resolve eq6710 eq6713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6710 eq6713
  have eq6899 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6894
  have eq6909 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6899 eq31
    | exact resolve eq31 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6929 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6899 eq2818
    | (have r₁ := eq2818
       have r₂ := eq6899
       grind)
    | exact resolve eq2818 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq6933 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6899 eq3660
    | exact resolve eq3660 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3660
  have eq6946 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6933
  have eq6950 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6929
  have eq6951 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6950
  have eq6977 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6909
    | exact resolve eq6909 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6909
  have eq7505 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6951 eq868
    | exact resolve eq868 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq7522 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7505
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7505
       have r₂ := eq13 x y
       grind)
    | exact resolve eq7505 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505
  have eq7526 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6946 eq7522
    | exact resolve eq7522 eq6946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6946 eq7522
  have eq7536 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6977
       grind)
    | exact superpose eq6977 eq18
    | exact resolve eq18 eq6977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7537 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6977
       grind)
    | exact superpose eq6977 eq24
    | exact resolve eq24 eq6977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7540 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq184
       have i₂ := eq6977
       grind)
    | exact superpose eq6977 eq184
    | (have r₁ := eq184
       have r₂ := eq6977
       grind)
    | exact resolve eq184 eq6977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq7544 : (k x (M.op x y)) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq7540
  have eq7547 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7537
    | exact resolve eq7537 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537
  have eq7548 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq186 eq7536
    | exact resolve eq7536 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq7536
  have eq7717 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7526 eq141
    | exact resolve eq141 eq7526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7526
  have eq7730 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq7717
    | exact resolve eq7717 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7717
  have eq7746 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7548 eq879
    | exact resolve eq879 eq7548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq7768 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq7746
  have eq8108 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7768 eq39
    | exact resolve eq39 eq7768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7768
  have eq8115 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq8108
    | exact resolve eq8108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8108
  have eq8117 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7547 eq8115
    | exact resolve eq8115 eq7547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8115
  have eq8175 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8117 eq824
    | exact resolve eq824 eq8117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824 eq8117
  have eq8185 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8175
  have eq8194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3575 eq8185
    | exact resolve eq8185 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8185
  have eq8195 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8194
  have eq8284 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8195 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq8195
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq8195
       grind)
    | exact resolve eq12 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8286 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8195 eq16
    | exact resolve eq16 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8295 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8195 eq181
    | exact resolve eq181 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8304 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8284
  have eq8317 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8195 eq8295
    | exact resolve eq8295 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8295
  have eq8326 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq8286
    | (have j0 := eq8286 X0
       grind)
    | exact resolve eq8286 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8286
  have eq8327 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8304
    | exact resolve eq8304 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8304
  have eq8328 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8327
  have eq8335 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8317 eq8326
    | exact resolve eq8326 eq8317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8317 eq8326
  have eq8336 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8328
    | exact resolve eq8328 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8328
  have eq8339 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8335 eq8336
    | exact resolve eq8336 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8336
  have eq8342 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8335 eq27
    | exact resolve eq27 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8335
  have eq8390 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7547 eq8342
    | (have r₁ := eq8342
       have r₂ := eq7547
       grind)
    | exact resolve eq8342 eq7547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8342
  have eq8391 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8390
  have eq8392 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8391
  have eq8393 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6951 eq8392
    | exact resolve eq8392 eq6951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951 eq8392
  have eq8394 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8393
  have eq8399 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8394 eq27
    | exact resolve eq27 eq8394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8428 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7547 eq8399
    | exact resolve eq8399 eq7547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8399
  have eq8429 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8428
  have eq8625 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8339 eq152
    | exact resolve eq152 eq8339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8339
  have eq8638 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8625
    | exact resolve eq8625 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8625
  have eq8643 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3575 eq8638
    | exact resolve eq8638 eq3575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3575 eq8638
  have eq8646 : x = (k x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8394 eq8643
    | exact resolve eq8643 eq8394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8394 eq8643
  have eq8680 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8646 eq41
    | exact resolve eq41 eq8646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8646
  have eq8689 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8680
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8680
    | exact resolve eq8680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8680
  have eq8693 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq7547 eq8689
    | exact resolve eq8689 eq7547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7547 eq8689
  have eq8702 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8693
  have eq8706 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq8702
       have r₂ := eq8429
       grind)
    | exact resolve eq8702 eq8429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8429 eq8702
  have eq8800 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8706 eq152
    | exact resolve eq152 eq8706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq8706
  have eq8812 : x = (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq8800
    | exact resolve eq8800 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8800
  have eq8818 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq6977 eq8812
    | exact resolve eq8812 eq6977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6977 eq8812
  have eq10795 : x ≠ (k x (M.op x y)) ∨ (k x x) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq7544
       grind)
    | exact superpose eq7544 eq13
    | exact resolve eq13 eq7544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7544
  have eq10839 : (k x x) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10795
       have r₂ := eq8818
       grind)
    | exact resolve eq10795 eq8818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10795
  have eq10863 : x = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8818 eq10839
    | exact resolve eq10839 eq8818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8818 eq10839
  have eq10885 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7730 eq10863
    | exact resolve eq10863 eq7730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7730 eq10863
  have eq10886 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq10885
  have eq10920 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq865 x x
       have i₂ := eq10886
       grind)
    | exact superpose eq10886 eq865
    | (have j0 := eq865 x x
       grind)
    | (have r₁ := eq865 x x
       have r₂ := eq10886
       grind)
    | exact resolve eq865 eq10886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10886
  have eq10921 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10920
  have eq10922 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq10921
  have eq10935 : (M.op (M.op x y) x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq10922
       grind)
    | exact superpose eq10922 eq179
    | exact resolve eq179 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq10972 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10922 eq10935
    | exact resolve eq10935 eq10922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10935
  have eq11031 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10972 eq7548
    | exact resolve eq7548 eq10972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7548 eq10972
  have eq11055 : x = (M.op x y) ∨ x = y := by grind
  clear eq11031
  have eq11097 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11055
       grind)
    | exact superpose eq11055 eq18
    | exact resolve eq18 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11098 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq11055
       grind)
    | exact superpose eq11055 eq22
    | exact resolve eq22 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11126 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq11098
    | exact resolve eq11098 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11098
  have eq11141 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11126 eq3342
    | (have r₁ := eq3342
       have r₂ := eq11126
       grind)
    | exact resolve eq3342 eq11126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq11153 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11141
  have eq11159 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8195 eq11153
    | exact resolve eq11153 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8195 eq11153
  have eq11160 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11159
  have eq13755 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11160 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11160
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11160
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11160
       grind)
    | exact resolve eq12 eq11160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11160
  have eq13779 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13755
  have eq13808 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13779
    | exact resolve eq13779 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13779
  have eq13809 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq13808
  have eq13819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13809
    | exact resolve eq13809 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13809
  have eq13823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3286 eq13819
    | exact resolve eq13819 eq3286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3286 eq13819
  have eq13826 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13823
       have r₂ := eq27
       grind)
    | exact resolve eq13823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13823
  have eq13829 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13826 eq27
    | exact resolve eq27 eq13826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13831 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13826 eq200
    | exact resolve eq200 eq13826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq13840 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13826 eq950
    | (have r₁ := eq950
       have r₂ := eq13826
       grind)
    | exact resolve eq950 eq13826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq13849 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13840
  have eq13863 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13831
    | exact resolve eq13831 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13831
  have eq13873 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13826 eq13863
    | exact resolve eq13863 eq13826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13826 eq13863
  have eq13876 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11126 eq13829
    | exact resolve eq13829 eq11126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11126
  have eq29802 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13873 eq13849
    | exact resolve eq13849 eq13873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13849 eq13873
  have eq29888 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq29802
  have eq29964 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29888 eq1960
    | exact resolve eq1960 eq29888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq29981 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29888 eq141
    | exact resolve eq141 eq29888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq29888
  have eq29995 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq29964
  have eq30001 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq29981
    | exact resolve eq29981 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq29981
  have eq30003 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq29995
       have r₂ := eq13829
       grind)
    | exact resolve eq29995 eq13829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13829 eq29995
  have eq30007 : y = (k y (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6899 eq30001
    | exact resolve eq30001 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30001
  have eq30009 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6899 eq30003
    | exact resolve eq30003 eq6899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6899 eq30003
  have eq30147 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30009 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq30009
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq30009
       grind)
    | exact resolve eq13 eq30009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30148 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq30009 eq16
    | exact resolve eq16 eq30009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30009
  have eq30171 : (k y (M.op x y)) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq30147
  have eq30199 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30007 eq30171
    | exact resolve eq30171 eq30007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30007 eq30171
  have eq30303 : ∀ X0 : G, (M.op y y) = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq181 y X0 y
       have i₂ := eq30199
       grind)
    | exact superpose eq30199 eq181
    | exact resolve eq181 eq30199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq30346 : (M.op y y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30148 eq30303
    | exact resolve eq30303 eq30148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30148 eq30303
  have eq30356 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30199 eq30346
    | exact resolve eq30346 eq30199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30199 eq30346
  have eq30576 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq30356 eq11097
    | exact resolve eq11097 eq30356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11097 eq30356
  have eq30627 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq30576
  have eq30663 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq30627
       have r₂ := eq13876
       grind)
    | exact resolve eq30627 eq13876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13876 eq30627
  have eq30715 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq30663
  have eq30718 : x = y := by
    first
    | (have r₁ := eq30715
       have r₂ := eq11055
       grind)
    | exact resolve eq30715 eq11055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11055 eq30715
  have eq30726 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq30718
       grind)
    | exact superpose eq30718 eq18
    | exact resolve eq18 eq30718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq30727 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq30718
       grind)
    | exact superpose eq30718 eq24
    | exact resolve eq24 eq30718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq30718
  have eq30832 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30727
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30727
    | exact resolve eq30727 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30727
  have eq30854 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30832 eq26
    | exact resolve eq26 eq30832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq30832
  have eq31103 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10922
       have i₂ := eq30726
       grind)
    | exact superpose eq30726 eq10922
    | exact resolve eq10922 eq30726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10922
  have eq31138 : x = (M.op x y) := by grind
  clear eq31103
  have eq31183 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31138
       grind)
    | exact superpose eq31138 eq22
    | exact resolve eq22 eq31138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq31193 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ x) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq350
       have i₂ := eq31138
       grind)
    | exact superpose eq31138 eq350
    | exact resolve eq350 eq31138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq31213 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq30726
       have i₂ := eq31138
       grind)
    | exact superpose eq31138 eq30726
    | exact resolve eq30726 eq31138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30726 eq31138
  have eq31222 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq31213 eq31193
    | exact resolve eq31193 eq31213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31193 eq31213
  have eq31235 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq31222
    | exact resolve eq31222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31222
  have eq31240 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq31183 eq20
    | exact resolve eq20 eq31183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31183
  have eq31665 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq31235 eq865
    | (have j0 := eq865 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq865 eq31235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq31235
  have eq31666 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq31665
       have r₂ := eq31240
       grind)
    | exact resolve eq31665 eq31240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31665
  have eq31672 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq31240 eq31666
    | exact resolve eq31666 eq31240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31666
  have eq31678 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq30854 eq31672
    | exact resolve eq31672 eq30854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31672
  have eq31682 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31240 eq31678
    | exact resolve eq31678 eq31240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31678
  have eq31684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30854 eq31682
    | exact resolve eq31682 eq30854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30854 eq31682
  have eq31685 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31684
  have eq31694 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq31685 eq27
    | exact resolve eq27 eq31685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq31685
  have eq31726 : False := by grind
  exact eq31726

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_x_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 X1 X2 X3
       have i₂ := eq63 X1 (M.op X1 X2) X3 X0
       grind)
    | (have i₁ := eq65 X1 X2 X3
       have i₂ := eq63 X0 (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq63 eq65
    | exact resolve eq65 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X1 X2 X0
       have i₂ := eq9 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq258 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op X2 (M.op X2 (M.op X3 (M.op X1 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq114 X2 (M.op X3 (M.op X1 X4)) X0
       have i₂ := eq112 X3 X1 X4 X0
       grind)
    | exact superpose eq112 eq114
    | exact resolve eq114 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq260 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114 X2 X2 X1
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X3)) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq258 X0 X1 X2 X3 x
       have i₂ := eq114 X2 X3 (M.op X1 x)
       grind)
    | exact superpose eq114 eq258
    | exact resolve eq258 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq301 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 X0)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq293 X3 x X2 X0
       have i₂ := eq114 X2 X3 (M.op X3 x)
       grind)
    | exact superpose eq114 eq293
    | exact resolve eq293 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq293
  have eq318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq301 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq301
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq394 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X4) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq318 X0 X1 X2 x
       have i₂ := eq318 X3 X4 X2 x
       grind)
    | exact superpose eq318 eq318
    | exact resolve eq318 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) X0) X0
       have i₂ := eq260 X1 X2 X0
       grind)
    | (have i₁ := eq12 (M.op X2 X2) X2
       have i₂ := eq260 X0 X1 X2
       grind)
    | exact superpose eq260 eq12
    | (have j0 := eq12 (M.op (M.op X1 X2) X0) X0
       grind)
    | exact resolve eq12 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq488 X0 X1 X2
       grind)
    | (have r₁ := eq488 x X0 X1
       have r₂ := eq318 X0 X1 x x
       grind)
    | exact resolve eq488 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq583 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq509 x X0 X1
       have i₂ := eq318 X0 X1 x x
       grind)
    | exact superpose eq318 eq509
    | exact resolve eq509 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X1) (σ X2))) = (k (τ (M.op (M.op X0 X1) (σ X2))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X0 X1) (σ X2)) X2
       have i₂ := eq509 (σ X2) X0 X1
       grind)
    | exact superpose eq509 eq22
    | exact resolve eq22 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (τ (M.op (σ X0) (M.op (σ X0) X1))) = (k (τ (M.op (σ X0) (M.op (σ X0) X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) (M.op (σ X0) X1)) X0
       have i₂ := eq583 (σ X0) X1
       grind)
    | exact superpose eq583 eq22
    | exact resolve eq22 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq583
  have eq925 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2478 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq925
    | (have j0 := eq925 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq925 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2478 x y
       grind)
    | exact superpose eq2478 eq16
    | (have j1 := eq2478 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2478 x y
       grind)
    | exact resolve eq16 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq14661 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq14563
  have eq24698 : (τ (M.op (σ y) (σ x))) = (k (τ (M.op (σ y) (σ x))) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq686 y (σ x)
       have i₂ := eq14661
       grind)
    | exact superpose eq14661 eq686
    | exact resolve eq686 eq14661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq24875 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq14661 eq24698
    | exact resolve eq24698 eq14661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14661 eq24698
  have eq24898 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq24875
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24875
    | exact resolve eq24875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24875
  have eq24901 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq24898
       have r₂ := eq12 x y
       grind)
    | exact resolve eq24898 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24898
  have eq24916 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (σ x) X0) ∨ x = (k x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 (σ x) (σ y) X0 X1 X2
       have i₂ := eq24901
       grind)
    | exact superpose eq24901 eq394
    | exact resolve eq394 eq24901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25803 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq24901
       have i₂ := eq24916 (σ y) X0 X1
       grind)
    | exact superpose eq24916 eq24901
    | exact resolve eq24901 eq24916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24901 eq24916
  have eq25987 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 X1) (σ y)) ∨ x = (k x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq25803 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25803
  have eq26083 : (τ (σ x)) = (k (τ (σ x)) y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq590 x x y
       have i₂ := eq25987 x x
       grind)
    | exact superpose eq25987 eq590
    | exact resolve eq590 eq25987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq25987
  have eq26292 : x = (k x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26083
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq26083
    | exact resolve eq26083 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26083
  have eq26293 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq26292
  have eq26333 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq26293
       grind)
    | exact superpose eq26293 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq26293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26293
  have eq26334 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq26333
  have eq26344 : ∀ X0 X1 : G, (M.op y x) = (M.op (M.op X0 X1) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1 y x
       have i₂ := eq26334
       grind)
    | exact superpose eq26334 eq318
    | exact resolve eq318 eq26334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26468 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26334 eq26344
    | exact resolve eq26344 eq26334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26344
  have eq26502 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26468 y x
       have i₂ := eq26334
       grind)
    | exact superpose eq26334 eq26468
    | exact resolve eq26468 eq26334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26334 eq26468
  have eq26671 : x = (M.op x y) := by grind
  clear eq26502
  have eq26729 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26671
       grind)
    | exact superpose eq26671 eq16
    | exact resolve eq16 eq26671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26736 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq318 x y X0 X1
       have i₂ := eq26671
       grind)
    | exact superpose eq26671 eq318
    | exact resolve eq318 eq26671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq26741 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op x X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq394 x y X0 X1 X2
       have i₂ := eq26671
       grind)
    | exact superpose eq26671 eq394
    | exact resolve eq394 eq26671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq27828 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq26741 y X0 X1
       have i₂ := eq26671
       grind)
    | exact superpose eq26671 eq26741
    | exact resolve eq26741 eq26671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26671
  have eq28403 : x = (k x y) := by
    first
    | (have i₁ := eq509 y x x
       have i₂ := eq27828 x x
       grind)
    | exact superpose eq27828 eq509
    | exact resolve eq509 eq27828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq27828
  have eq28619 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq925 x y
       have i₂ := eq28403
       grind)
    | exact superpose eq28403 eq925
    | (have j0 := eq925 x y
       grind)
    | exact resolve eq925 eq28403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq28403
  have eq28622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq28619
  have eq28624 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq28622
       have r₂ := eq26729
       grind)
    | exact resolve eq28622 eq26729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28622
  have eq28974 : (M.op (σ y) (σ x)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq26736 (σ y) (σ x)
       have i₂ := eq28624
       grind)
    | exact superpose eq28624 eq26736
    | exact resolve eq26736 eq28624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26736
  have eq28975 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq26741 X0 (σ y) (σ x)
       have i₂ := eq28624
       grind)
    | exact superpose eq28624 eq26741
    | exact resolve eq26741 eq28624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26741
  have eq28978 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq28974
       have i₂ := eq28624
       grind)
    | exact superpose eq28624 eq28974
    | exact resolve eq28974 eq28624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28624 eq28974
  have eq29440 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq26729
       have i₂ := eq28975 (σ y)
       grind)
    | exact superpose eq28975 eq26729
    | exact resolve eq26729 eq28975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26729 eq28975
  have eq29761 : False := by grind
  exact eq29761

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation4419 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq43 X1 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq43 X0 X1
       grind)
    | exact resolve eq47 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq47
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53
  have eq206 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq210 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq206 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq206 X0 X0
       have r₂ := eq55 X0 X0
       grind)
    | exact resolve eq206 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq206
  have eq480 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq210 (σ X0) (σ X1)
       grind)
    | exact superpose eq210 eq15
    | exact resolve eq15 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq480 X0 X1
       have i₂ := eq210 X0 X1
       grind)
    | exact superpose eq210 eq480
    | exact resolve eq480 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq480
  have eq487 : False := by grind
  exact eq487

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq90 : y ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y x) := by
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
  have eq91 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : (M.op x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq228 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq59
    | (have j0 := eq59 (σ x)
       grind)
    | exact resolve eq59 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq10721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10721
    | exact resolve eq10721 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10721
  have eq10725 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq10722
       have r₂ := eq28
       grind)
    | exact resolve eq10722 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10722
  have eq10727 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10725
    | exact resolve eq10725 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10725
  have eq10730 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10727 eq91
    | (have r₁ := eq91
       have r₂ := eq10727
       grind)
    | exact resolve eq91 eq10727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq10731 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10727 eq228
    | exact resolve eq228 eq10727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq10727
  have eq10751 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10730
  have eq10752 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10751
  have eq10762 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq10731
    | exact resolve eq10731 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10731
  have eq10902 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10752 eq80
    | exact resolve eq80 eq10752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq10752
  have eq10906 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10902
  have eq10912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq10906 eq10762
    | exact resolve eq10762 eq10906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10762 eq10906
  have eq10932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq10912
  have eq10948 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq10932
       have r₂ := eq28
       grind)
    | exact resolve eq10932 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10932
  have eq10958 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq10948 eq30
    | exact resolve eq30 eq10948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10948
  have eq10995 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq10958
    | exact resolve eq10958 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10958
  have eq10996 : y = (M.op x y) ∨ x = y := by grind
  clear eq10995
  have eq11004 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq10996 eq21
    | exact resolve eq21 eq10996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11006 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10996 eq90
    | (have r₁ := eq90
       have r₂ := eq10996
       grind)
    | exact resolve eq90 eq10996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq11012 : (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq10996 eq217
    | exact resolve eq217 eq10996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq10996
  have eq11043 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y x) := by grind
  clear eq11006
  have eq11044 : (k x y) = (M.op y x) ∨ x = y := by grind
  clear eq11043
  have eq11066 : (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11012
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11012
    | exact resolve eq11012 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012
  have eq11073 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11004
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11004
    | exact resolve eq11004 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11004
  have eq11246 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11044
       grind)
    | exact superpose eq11044 eq49
    | exact resolve eq49 eq11044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11044
  have eq12683 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq11246
       have i₂ := eq11066
       grind)
    | exact superpose eq11066 eq11246
    | exact resolve eq11246 eq11066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11066 eq11246
  have eq12709 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq12683
  have eq12716 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq12709
    | exact resolve eq12709 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12709
  have eq12733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12716 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12716
  have eq12740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12733
    | exact resolve eq12733 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12733
  have eq12743 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12740
       have r₂ := eq28
       grind)
    | exact resolve eq12740 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12740
  have eq12745 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq12743
    | exact resolve eq12743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12743
  have eq12941 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12745 eq28
    | exact resolve eq28 eq12745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12745
  have eq12979 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq12941
       have r₂ := eq11073
       grind)
    | exact resolve eq12941 eq11073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11073 eq12941
  have eq12990 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq12979 eq30
    | exact resolve eq30 eq12979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12979
  have eq13055 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq12990
    | exact resolve eq12990 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12990
  have eq13056 : x = y := by grind
  clear eq13055
  have eq13064 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq13056
       grind)
    | exact superpose eq13056 eq19
    | exact resolve eq19 eq13056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq13065 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq13056
       grind)
    | exact superpose eq13056 eq25
    | exact resolve eq25 eq13056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq13056
  have eq13107 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13065
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13065
    | exact resolve eq13065 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq13065
  have eq13112 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13107 eq27
    | exact resolve eq27 eq13107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq13107
  have eq13211 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq13112 eq71
    | exact resolve eq71 eq13112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq13112
  have eq13248 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13211
       have i₂ := eq13064
       grind)
    | exact superpose eq13064 eq13211
    | exact resolve eq13211 eq13064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13064 eq13211
  have eq13259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13248 eq15
    | exact resolve eq15 eq13248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13248
  have eq13302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13259
    | exact resolve eq13259 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq13259
  have eq13311 : False := by grind
  exact eq13311

/-- `Equation4419`: `x ◇ (x ◇ y) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_pyx_pxy_Equation4419 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4419 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4419.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X1) X0) := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X2) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X2 X1) X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) (M.op X2 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 X1) X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 X3
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X2 X1))) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X1) X2
       have i₂ := eq14 X2 X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 (M.op X0 y)) = (M.op (M.op x y) X0) := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq95 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq95
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq99
  have eq121 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq122
  have eq126 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq125
  have eq132 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq16
    | exact resolve eq16 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq217 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1
       have i₂ := eq14 X1 y X0
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 y))) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 y) X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0
       have i₂ := eq14 X0 sF3 x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq307 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq296 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq296
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq308 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq307
  have eq386 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq58 (M.op X0 y)
       have i₂ := eq217 X0 y
       grind)
    | (have i₁ := eq58 (M.op x y)
       have i₂ := eq217 X0 y
       grind)
    | exact superpose eq217 eq58
    | exact resolve eq58 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op X0 y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq59 (M.op X0 y)
       have i₂ := eq217 X0 sF3
       grind)
    | (have i₁ := eq59 (M.op x y)
       have i₂ := eq217 X0 sF3
       grind)
    | exact superpose eq217 eq59
    | exact resolve eq59 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq387 X0
       have i₂ := eq217 X0 (M.op sF0 sF3)
       grind)
    | (have i₁ := eq387 x
       have i₂ := eq217 X0 (M.op sF0 sF3)
       grind)
    | exact superpose eq217 eq387
    | exact resolve eq387 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq389 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq386 X0
       have i₂ := eq217 X0 (M.op sF0 y)
       grind)
    | (have i₁ := eq386 x
       have i₂ := eq217 X0 (M.op sF0 y)
       grind)
    | exact superpose eq217 eq386
    | exact resolve eq386 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq397 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq59 eq388
    | exact resolve eq388 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq398 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq389 X0
       have i₂ := eq58 sF0
       grind)
    | exact superpose eq58 eq389
    | exact resolve eq389 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq425 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq443 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq226 eq58
    | exact resolve eq58 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq226 eq59
    | exact resolve eq59 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq226 eq444
    | exact resolve eq444 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq446 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) y)) := by
    intro X0
    first
    | exact superpose eq226 eq443
    | exact resolve eq443 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq454 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq59 eq445
    | exact resolve eq445 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq455 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq446 X0
       have i₂ := eq58 sF4
       grind)
    | exact superpose eq58 eq446
    | exact resolve eq446 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq530 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq397 sF4
       have i₂ := eq58 sF4
       grind)
    | exact superpose eq58 eq397
    | exact resolve eq397 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 y)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 (M.op X0 y) X1 X2
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X0) X3) = (M.op (M.op X0 (M.op X0 X1)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq55 (M.op x X1) X0 X3 X4
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq764 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 y X0 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq53
    | exact resolve eq53 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) := by
    intro X0
    first
    | exact superpose eq226 eq765
    | (have j0 := eq765 X0 (σ x)
       grind)
    | exact resolve eq765 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq869 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq764 X0 x
       have i₂ := eq217 x X0
       grind)
    | (have i₁ := eq764 x x
       have i₂ := eq217 X0 x
       grind)
    | exact superpose eq217 eq764
    | (have j0 := eq764 X0 x
       grind)
    | exact resolve eq764 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1188 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq132 eq308
    | exact resolve eq308 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq308
  have eq1212 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq226 eq1188
    | exact resolve eq1188 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1213 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq454 eq1212
    | exact resolve eq1212 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1214 : (σ (M.op (M.op x y) (M.op y y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1213
       have i₂ := eq217 y (M.op y y)
       grind)
    | exact superpose eq217 eq1213
    | exact resolve eq1213 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1215 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq398 eq1214
    | exact resolve eq1214 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1216 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq126 eq1215
    | exact resolve eq1215 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1332 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (M.op X0 X1)
       have i₂ := eq54 X1 y (M.op X0 X1) X0
       grind)
    | exact superpose eq54 eq58
    | exact resolve eq58 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1333 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op x X0)
       have i₂ := eq54 X0 sF3 (M.op x X0) x
       grind)
    | exact superpose eq54 eq59
    | exact resolve eq59 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1381 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X1 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq226 eq1333
    | exact resolve eq1333 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1382 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op X1 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1332 X0 X1
       have i₂ := eq217 (M.op X0 X1) (M.op X1 (M.op X1 y))
       grind)
    | exact superpose eq217 eq1332
    | exact resolve eq1332 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332
  have eq1407 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq59 eq1381
    | exact resolve eq1381 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1408 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1382 X0 X1
       have i₂ := eq58 X1
       grind)
    | exact superpose eq58 eq1382
    | exact resolve eq1382 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq2211 : (M.op (M.op x y) y) = (M.op y (M.op (M.op (σ x) (σ y)) y)) := by
    first
    | (have i₁ := eq868 y
       have i₂ := eq217 sF4 y
       grind)
    | exact superpose eq217 eq868
    | exact resolve eq868 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2212 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq226 eq868
    | exact resolve eq868 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq2300 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2212 eq53
    | exact resolve eq53 eq2212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq2325 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq2300 X0
       have i₂ := eq14 sF4 sF3 sF4
       grind)
    | exact superpose eq14 eq2300
    | exact resolve eq2300 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2300
  have eq2331 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | (have i₁ := eq2325 x
       have i₂ := eq14 sF4 sF3 x
       grind)
    | exact superpose eq14 eq2325
    | exact resolve eq2325 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq2332 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq454 eq2331
    | exact resolve eq2331 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331
  have eq2333 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1216 eq2332
    | exact resolve eq2332 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332
  have eq2344 : (M.op (M.op x y) y) = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq869 y
       have i₂ := eq217 sF0 y
       grind)
    | exact superpose eq217 eq869
    | exact resolve eq869 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2345 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op x y) (σ y))) := by
    first
    | exact superpose eq226 eq869
    | exact resolve eq869 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2399 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2344 eq53
    | exact resolve eq53 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2424 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op X0 y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2399 X0
       have i₂ := eq14 sF0 y sF0
       grind)
    | exact superpose eq14 eq2399
    | exact resolve eq2399 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2430 : (M.op (M.op x y) (M.op (M.op x y) y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2424 x
       have i₂ := eq14 sF0 y x
       grind)
    | exact superpose eq14 eq2424
    | exact resolve eq2424 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq2431 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq398 eq2430
    | exact resolve eq2430 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2433 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2345 eq53
    | exact resolve eq53 eq2345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2345
  have eq2457 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op X0 (σ y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2433 X0
       have i₂ := eq14 sF0 sF3 sF4
       grind)
    | exact superpose eq14 eq2433
    | exact resolve eq2433 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2463 : (M.op (M.op x y) (M.op (M.op x y) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (σ y)))) := by
    first
    | (have i₁ := eq2457 x
       have i₂ := eq14 sF0 sF3 x
       grind)
    | exact superpose eq14 eq2457
    | exact resolve eq2457 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2464 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq455 eq2463
    | exact resolve eq2463 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq2463
  have eq2573 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq59 eq1407
    | exact resolve eq1407 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1407
  have eq2671 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq454 eq2573
    | exact resolve eq2573 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq2573
  have eq2688 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1216 eq2671
    | exact resolve eq2671 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq2671
  have eq2696 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq2333 eq2688
    | exact resolve eq2688 eq2333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333 eq2688
  have eq2718 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2696 y
       have i₂ := eq58 sF4
       grind)
    | exact superpose eq58 eq2696
    | exact resolve eq2696 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq2696
  have eq2815 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq530 eq1408
    | exact resolve eq1408 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq2896 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2464 eq2815
    | exact resolve eq2815 eq2464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2464 eq2815
  have eq2926 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2431 eq2896
    | exact resolve eq2896 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431 eq2896
  have eq3022 : (M.op y (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq2211 eq220
    | exact resolve eq220 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq3134 : (M.op y (M.op (M.op x y) y)) = (M.op y (M.op y (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3022
       have i₂ := eq14 y sF4 sF0
       grind)
    | exact superpose eq14 eq3022
    | exact resolve eq3022 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3191 : (M.op (M.op x y) y) = (M.op y (M.op y (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq2344 eq3134
    | exact resolve eq3134 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134
  have eq4223 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) (M.op y y))) X0) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq425 (M.op y y) X0
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq425
    | exact resolve eq425 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq425
  have eq4398 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op y y) (M.op y y))) X0) := by
    intro X0
    first
    | exact superpose eq229 eq4223
    | exact resolve eq4223 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq4223
  have eq4433 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op y y))) X0) := by
    intro X0
    first
    | (have i₁ := eq4398 X0
       have i₂ := eq217 y (M.op y y)
       grind)
    | exact superpose eq217 eq4398
    | exact resolve eq4398 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4398
  have eq4450 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (σ (M.op (M.op x y) (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq398 eq4433
    | exact resolve eq4433 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq4433
  have eq4462 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq126 eq4450
    | exact resolve eq4450 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq4450
  have eq4466 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq226 eq4462
    | exact resolve eq4462 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226 eq4462
  have eq4468 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq2718 eq4466
    | exact resolve eq4466 eq2718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2718 eq4466
  have eq4470 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq2926 eq4468
    | exact resolve eq4468 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926 eq4468
  have eq4742 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (M.op x y) y))) = (M.op (M.op (M.op X1 (M.op y (M.op (σ x) (σ y)))) y) X0) := by
    intro X0 X1
    first
    | exact superpose eq3191 eq56
    | exact resolve eq56 eq3191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3191
  have eq4749 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op X0 (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq4742 x x
       have i₂ := eq217 (M.op x (M.op y sF4)) x
       grind)
    | exact superpose eq217 eq4742
    | exact resolve eq4742 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq4742
  have eq4762 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq4749 x
       have i₂ := eq220 sF0 x
       grind)
    | exact superpose eq220 eq4749
    | exact resolve eq4749 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq4749
  have eq4766 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq4470 eq4762
    | exact resolve eq4762 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4762
  have eq5004 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 y)) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq1408 eq535
    | exact resolve eq535 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq5162 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (M.op x y) (M.op X0 y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq4470 eq5004
    | exact resolve eq5004 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470 eq5004
  have eq5228 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5162 X0 X1
       have i₂ := eq535 X0 X1 sF0
       grind)
    | exact superpose eq535 eq5162
    | exact resolve eq5162 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq5162
  have eq5278 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq4766 eq5228
    | exact resolve eq5228 eq4766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5228
  have eq5591 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq4766 eq536
    | exact resolve eq536 eq4766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq4766
  have eq5592 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X1) = (M.op (M.op X2 (M.op X0 (σ y))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq5278 eq5591
    | exact resolve eq5591 eq5278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5278 eq5591
  have eq5652 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5592 X0 x X0
       have i₂ := eq57 X0 sF3 x
       grind)
    | exact superpose eq57 eq5592
    | exact resolve eq5592 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq6115 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq5592 eq539
    | exact resolve eq539 eq5592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq5592
  have eq20020 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20021 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq20020
    | exact resolve eq20020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20020
  have eq20032 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq20021
       have r₂ := eq28
       grind)
    | exact resolve eq20021 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20021
  have eq20037 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20032 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq20032
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20032
       grind)
    | exact resolve eq12 eq20032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20032
  have eq20054 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq20037
  have eq20055 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq20054
  have eq20080 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20055 eq79
    | exact resolve eq79 eq20055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq20055
  have eq20089 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20080
  have eq20118 : (M.op y x) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5652 y x
       have i₂ := eq20089
       grind)
    | exact superpose eq20089 eq5652
    | exact resolve eq5652 eq20089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20119 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6115 X0 y x
       have i₂ := eq20089
       grind)
    | exact superpose eq20089 eq6115
    | exact resolve eq6115 eq20089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6115
  have eq20424 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20119 eq20118
    | exact resolve eq20118 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20118 eq20119
  have eq20519 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20424
  have eq20552 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20519
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20519
    | exact resolve eq20519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20519
  have eq20633 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20089
       have i₂ := eq20552
       grind)
    | exact superpose eq20552 eq20089
    | exact resolve eq20089 eq20552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20089 eq20552
  have eq20650 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20633
  have eq20667 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20650 eq30
    | exact resolve eq30 eq20650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20650
  have eq20787 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20667
    | exact resolve eq20667 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667
  have eq20788 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq20787
  have eq20811 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20788 eq29
    | exact resolve eq29 eq20788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20788
  have eq20928 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq20811
    | exact resolve eq20811 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20811
  have eq20929 : x = (M.op x y) ∨ x = y := by grind
  clear eq20928
  have eq20986 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20929 eq21
    | exact resolve eq21 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21042 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20929 eq2344
    | exact resolve eq2344 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344
  have eq21104 : (M.op x y) = (M.op y (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq21042
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21042
    | exact resolve eq21042 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21042
  have eq21153 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq20986
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20986
    | exact resolve eq20986 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20986
  have eq21188 : (k x y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = y := by
    first
    | exact superpose eq21153 eq63
    | exact resolve eq63 eq21153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21297 : (k x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq146 eq21188
    | exact resolve eq21188 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21188
  have eq21357 : x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20929 eq21104
    | exact resolve eq21104 eq20929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20929 eq21104
  have eq21375 : x = (M.op y x) ∨ x = y := by grind
  clear eq21357
  have eq21481 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq21375
       grind)
    | exact superpose eq21375 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21375
       grind)
    | exact resolve eq12 eq21375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21375
  have eq21497 : x ≠ x ∨ x = y ∨ x = (k x y) := by grind
  clear eq21481
  have eq21498 : x = (k x y) ∨ x = y := by grind
  clear eq21497
  have eq21520 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq21498
       grind)
    | exact superpose eq21498 eq49
    | exact resolve eq49 eq21498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21498
  have eq21536 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq21520
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21520
    | exact resolve eq21520 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21520
  have eq21543 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21153 eq21536
    | exact resolve eq21536 eq21153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21536
  have eq21563 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq21543
  have eq21579 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21563 eq146
    | exact resolve eq146 eq21563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq21563
  have eq21594 : (M.op x y) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq31 eq21579
    | exact resolve eq21579 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21579
  have eq22663 : (M.op x y) = (k x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21297 eq21594
    | exact resolve eq21594 eq21297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21297 eq21594
  have eq22667 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq22663
  have eq22682 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq22667
       grind)
    | exact superpose eq22667 eq49
    | exact resolve eq49 eq22667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq22667
  have eq22710 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq22682
    | exact resolve eq22682 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22682
  have eq22743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22710 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq22710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22710
  have eq22759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq22743
    | exact resolve eq22743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22743
  have eq22770 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq22759
       have r₂ := eq28
       grind)
    | exact resolve eq22759 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22759
  have eq24597 : (M.op (σ y) (σ x)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq22770 eq5652
    | exact resolve eq5652 eq22770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652
  have eq63322 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq24597 eq22770
    | exact resolve eq22770 eq24597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24597
  have eq63354 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63322
  have eq63389 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63354 eq869
    | exact resolve eq869 eq63354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq63354
  have eq63462 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq63389
    | exact resolve eq63389 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63389
  have eq63561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63462 eq22770
    | exact resolve eq22770 eq63462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22770 eq63462
  have eq63592 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63561
  have eq63622 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63592 eq28
    | exact resolve eq28 eq63592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63592
  have eq63700 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq63622
       have r₂ := eq21153
       grind)
    | exact resolve eq63622 eq21153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21153 eq63622
  have eq63709 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq63700 eq30
    | exact resolve eq30 eq63700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq63700
  have eq63994 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq63709
    | exact resolve eq63709 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq63709
  have eq63995 : x = y := by grind
  clear eq63994
  have eq64019 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq63995
       grind)
    | exact superpose eq63995 eq19
    | exact resolve eq19 eq63995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq64020 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq63995
       grind)
    | exact superpose eq63995 eq25
    | exact resolve eq25 eq63995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq63995
  have eq64159 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq64020
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq64020
    | exact resolve eq64020 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq64020
  have eq64179 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq64159 eq27
    | exact resolve eq27 eq64159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq64159
  have eq64519 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq64179 eq71
    | exact resolve eq71 eq64179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq64179
  have eq64597 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq64519
       have i₂ := eq64019
       grind)
    | exact superpose eq64019 eq64519
    | exact resolve eq64519 eq64019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64019 eq64519
  have eq64618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64597 eq15
    | exact resolve eq15 eq64597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64597
  have eq64694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq64618
    | exact resolve eq64618 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq64618
  have eq64715 : False := by grind
  exact eq64715

/-- `Equation442`: `x = x ◇ (y ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation442 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law442 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law442.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq173 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq191 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq192 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq196 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq623 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq197 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq197
    | exact resolve eq197 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq197 x y
       grind)
    | exact superpose eq197 eq16
    | (have j1 := eq197 x y
       grind)
    | exact resolve eq16 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq658 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq623
    | (have j0 := eq623 X0 X1
       grind)
    | exact resolve eq623 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq623
  have eq659 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq658
    | exact resolve eq658 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq718 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq659 (τ X1) X0
       grind)
    | exact superpose eq659 eq18
    | (have j1 := eq659 (τ X1) X0
       grind)
    | exact resolve eq18 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq659
  have eq998 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq718 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq718
    | exact resolve eq718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1044 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq998
    | (have j0 := eq998 X0 X1
       grind)
    | exact resolve eq998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq637
       have i₂ := eq1044 y x
       grind)
    | exact superpose eq1044 eq637
    | (have j1 := eq1044 (σ y) (σ x)
       grind)
    | (have r₁ := eq637
       have r₂ := eq1044 y x
       grind)
    | exact resolve eq637 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1335 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1334
  have eq1341 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1335
  have eq1426 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq637
       have i₂ := eq1341
       grind)
    | exact superpose eq1341 eq637
    | exact resolve eq637 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq1341
  have eq1427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1426
  have eq1428 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1427
  have eq1518 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1428
  have eq1543 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1518
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1518
    | exact resolve eq1518 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1644 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1543
       grind)
    | exact superpose eq1543 eq16
    | exact resolve eq16 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1669 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1644
       have i₂ := eq1044 y x
       grind)
    | exact superpose eq1044 eq1644
    | (have j1 := eq1044 y x
       grind)
    | (have r₁ := eq1644
       have r₂ := eq1044 y x
       grind)
    | exact resolve eq1644 eq1044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1670 : y = (M.op x x) := by grind
  clear eq1669
  have eq1796 : (M.op x y) = (k y x) := by grind
  clear eq1670
  have eq1877 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1644
       have i₂ := eq1796
       grind)
    | exact superpose eq1796 eq1644
    | exact resolve eq1644 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644 eq1796
  have eq1880 : False := by grind
  exact eq1880
