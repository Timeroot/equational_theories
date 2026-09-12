import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq341 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq341 X0 X1
       have j1 := eq342 X0 X1
       grind)
    | (have r₁ := eq341 X0 X1
       have r₂ := eq342 X0 X1
       grind)
    | exact resolve eq341 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq342
  have eq404 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345 y (σ x)
       grind)
    | exact superpose eq345 eq16
    | (have j1 := eq345 y (σ x)
       grind)
    | exact resolve eq16 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq422 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq408
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq408
    | exact resolve eq408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq438 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq404 X0 X1
       grind)
    | exact superpose eq404 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq404 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq404 X0 X1
       grind)
    | exact resolve eq13 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq453 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq447 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq447 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq447 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq481 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq453 X1 (τ X0)
       grind)
    | exact superpose eq453 eq17
    | (have j1 := eq453 X1 (τ X0)
       grind)
    | exact resolve eq17 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq487 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq453 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq700 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq481 X1 (τ X0)
       grind)
    | exact superpose eq481 eq18
    | (have j1 := eq481 X1 (τ X0)
       grind)
    | exact resolve eq18 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq481
  have eq707 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq700 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq700
    | (have j0 := eq700 X0 X1
       grind)
    | exact resolve eq700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq722 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq707
    | (have j0 := eq707 X0 X1
       grind)
    | exact resolve eq707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq725 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq782 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 X1
       have i₂ := eq453 X0 X1
       grind)
    | exact superpose eq453 eq725
    | (have j0 := eq725 X1 X0
       have j1 := eq453 X1 X0
       grind)
    | exact resolve eq725 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453 eq725
  have eq845 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq782 X0 X1
       have j1 := eq487 X0 X1
       grind)
    | (have r₁ := eq782 X0 X1
       have r₂ := eq487 X0 X1
       grind)
    | exact resolve eq782 eq487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487 eq782
  have eq886 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq845 X1 (σ X0)
       grind)
    | exact superpose eq845 eq22
    | (have j1 := eq845 X1 (σ X0)
       grind)
    | exact resolve eq22 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq845
  have eq922 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq886 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq886
    | (have j0 := eq886 X0 X1
       grind)
    | exact resolve eq886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq941 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq922
    | (have j0 := eq922 X0 X1
       grind)
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1182 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq941
    | exact resolve eq941 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1251 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1182 x y
       grind)
    | exact superpose eq1182 eq16
    | (have j1 := eq1182 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1182 x y
       grind)
    | exact resolve eq16 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1267 : y = (k x y) := by grind
  clear eq1251
  have eq1382 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq422
       have i₂ := eq404 y x
       grind)
    | exact superpose eq404 eq422
    | (have j1 := eq404 y x
       grind)
    | exact resolve eq422 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1383 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1382
  have eq1385 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1383
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1383
    | exact resolve eq1383 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq1387 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1385
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1385
    | exact resolve eq1385 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq1389 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq422
       have i₂ := eq1387
       grind)
    | exact superpose eq1387 eq422
    | exact resolve eq422 eq1387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq1387
  have eq1396 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1389
  have eq1397 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1396
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1396
    | exact resolve eq1396 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1398 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1397
  have eq1400 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1398
       grind)
    | exact superpose eq1398 eq16
    | exact resolve eq16 eq1398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1416 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1400
       have i₂ := eq404 y x
       grind)
    | exact superpose eq404 eq1400
    | (have j1 := eq404 y x
       grind)
    | exact resolve eq1400 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq1417 : (M.op x y) = (k x y) := by grind
  clear eq1416
  have eq1420 : y = (M.op x y) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq1267
       grind)
    | exact superpose eq1267 eq1417
    | exact resolve eq1417 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq1417
  have eq1422 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1400
       have i₂ := eq1420
       grind)
    | exact superpose eq1420 eq1400
    | exact resolve eq1400 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq1420
  have eq1431 : False := by grind
  exact eq1431

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation426 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law426 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq114 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq115 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq37
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq37 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq116 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq641 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq116 X0 X1
       grind)
    | exact superpose eq116 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq116 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq116 (M.op (τ X1) X0) X1
       grind)
    | exact resolve eq13 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq644 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq641 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq645 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq720 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq798 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq115 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq115 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq115 (M.op (σ X1) X0) X1
       grind)
    | exact resolve eq13 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq802 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq803 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ X1) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq802 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq2153 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq645
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq2195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2153 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2153
    | (have j0 := eq2153 X0 X1
       grind)
    | exact resolve eq2153 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq3938 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq803 (σ X0) X1
       grind)
    | exact superpose eq803 eq28
    | (have j1 := eq803 (σ X1) X0
       grind)
    | exact resolve eq28 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq803
  have eq3998 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3938 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3938
    | (have j0 := eq3938 X0 X1
       grind)
    | exact resolve eq3938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938
  have eq4031 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3998 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3998
    | (have j0 := eq3998 X0 X1
       grind)
    | exact resolve eq3998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3998
  have eq4040 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4031 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4031
    | (have j0 := eq4031 X0 X1
       grind)
    | exact resolve eq4031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4315 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq4040 X1 X0
       grind)
    | exact superpose eq4040 eq11
    | (have j1 := eq4040 X1 X0
       grind)
    | exact resolve eq11 eq4040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq5188 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4315 y x
       grind)
    | exact superpose eq4315 eq16
    | (have j1 := eq4315 y x
       grind)
    | exact resolve eq16 eq4315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq5216 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5188
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq5188
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq5188
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5188
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5188 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq5188
       have i₂ := eq2195 y x
       grind)
    | exact superpose eq2195 eq5188
    | (have j1 := eq2195 y x
       grind)
    | (have r₁ := eq5188
       have r₂ := eq2195 y x
       grind)
    | (have r₁ := eq5188
       have r₂ := eq2195 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq5188
       have r₂ := eq2195 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq5188 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq5188
  have eq5220 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5217
  have eq5221 : x = y ∨ (σ x) = (σ y) ∨ x = (k y x) := by grind
  clear eq5220
  have eq5222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5216
  have eq5223 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5222
  have eq5227 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5221
       grind)
    | exact superpose eq5221 eq16
    | exact resolve eq16 eq5221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221
  have eq5228 : x = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5227
       have r₂ := eq22 x
       grind)
    | exact resolve eq5227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq5233 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq720 x y
       have i₂ := eq5228
       grind)
    | exact superpose eq5228 eq720
    | (have j0 := eq720 x y
       grind)
    | exact resolve eq720 eq5228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq5228
  have eq5239 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5233
  have eq5240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5239
  have eq5252 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5240
       grind)
    | exact superpose eq5240 eq16
    | exact resolve eq16 eq5240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq5269 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5252
       have i₂ := eq5223
       grind)
    | exact superpose eq5223 eq5252
    | exact resolve eq5252 eq5223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5223 eq5252
  have eq5270 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5269
  have eq5271 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq5270
  have eq5272 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5271
       grind)
    | exact superpose eq5271 eq16
    | exact resolve eq16 eq5271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5273 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq5272
       have r₂ := eq22 x
       grind)
    | exact resolve eq5272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5272
  have eq5274 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq16
    | exact resolve eq16 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5275 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq10
    | exact resolve eq10 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq5327 : x = y := by
    first
    | (have i₁ := eq5275
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5275
    | exact resolve eq5275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5275
  have eq5328 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5274
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5274
    | exact resolve eq5274 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5274
  have eq5329 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5328
       have i₂ := eq5327
       grind)
    | exact superpose eq5327 eq5328
    | exact resolve eq5328 eq5327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327 eq5328
  have eq5330 : False := by grind
  exact eq5330

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X0) X0
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X1) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq21 X0 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | (have i₁ := eq35 (M.op X1 X1) X1
       have i₂ := eq31 X0 (M.op X1 X1)
       grind)
    | exact superpose eq31 eq35
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq23 X0 X1
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq50 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq51 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq50
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq50
  have eq59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X0) X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq51
    | exact resolve eq51 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq67 X1 (τ X0)
       grind)
    | exact superpose eq67 eq18
    | exact resolve eq18 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq108 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq103
    | exact resolve eq103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq133 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
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
  have eq141 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq154 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 X2 : G, (k (τ X2) (k (τ X0) X1)) = (τ (k X2 (k X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 X2 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (M.op X0 X0) X1
       have i₂ := eq38 (σ X1) X0
       grind)
    | exact superpose eq38 eq107
    | exact resolve eq107 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq59
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq59
    | exact resolve eq59 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq21
    | (have j1 := eq59 X0 X0
       grind)
    | exact resolve eq21 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq59 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq201 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq211 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq141
    | exact resolve eq141 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 (M.op X1 (σ X0))
       have i₂ := eq51 X1 (σ X0)
       grind)
    | exact superpose eq51 eq141
    | exact resolve eq141 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq232 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq213
    | exact resolve eq213 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq642 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq194 (M.op X0 X0)
       have i₂ := eq38 (M.op X0 X0) X0
       grind)
    | exact superpose eq38 eq194
    | (have j0 := eq194 (M.op X0 X0)
       grind)
    | exact resolve eq194 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq651 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq720 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (σ (k (τ X0) (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq201 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq201
    | (have j0 := eq201 (τ X0) X1
       grind)
    | exact resolve eq201 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163 (σ X0) X1
       have i₂ := eq201 X0 X1
       grind)
    | exact superpose eq201 eq163
    | (have j1 := eq201 X0 X2
       grind)
    | exact resolve eq163 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq201
  have eq753 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq736 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq736
    | (have j0 := eq736 X0 X1 X2
       grind)
    | exact resolve eq736 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq759 : ∀ X0 X1 : G, (M.op X1 (k (σ (τ X0)) X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq720 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq720
    | (have j0 := eq720 X0 X1
       grind)
    | exact resolve eq720 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq720
  have eq761 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq759 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq759
    | (have j0 := eq759 X0 X1
       grind)
    | exact resolve eq759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq1128 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 (M.op X0 (τ X1)) X2
       have i₂ := eq133 X0 X1
       grind)
    | exact superpose eq133 eq141
    | (have j1 := eq133 X0 X1
       grind)
    | exact resolve eq141 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq141
  have eq1140 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op X0 (τ X1)) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1128 X0 X1 X2
       have i₂ := eq211 X0 X1 X2
       grind)
    | exact superpose eq211 eq1128
    | (have j0 := eq1128 X0 X1 X2
       grind)
    | exact resolve eq1128 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1128
  have eq1462 : ∀ X0 X1 X2 : G, (k X1 (σ (σ (k X0 X0)))) = X1 ∨ (k X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X1 (σ (k X0 X0))
       have i₂ := eq753 X0 X2 (σ (k X0 X0))
       grind)
    | exact superpose eq753 eq108
    | (have j1 := eq753 X1 (σ (σ (k X0 X0))) X2
       grind)
    | exact resolve eq108 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq2625 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X2) (k X0 (σ X1))
       have i₂ := eq176 X0 X1 X2
       grind)
    | exact superpose eq176 eq12
    | (have j0 := eq12 (σ X2) (k X0 (σ X1))
       have j1 := eq176 X0 X1 X2
       grind)
    | (have r₁ := eq12 (σ X2) (k X0 (σ X1))
       have r₂ := eq176 X0 X1 X2
       grind)
    | exact resolve eq12 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2627 : ∀ X0 X1 X2 : G, (k (σ X2) (k X0 (σ X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2625 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2628 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2627 X0 X1 X2
       have i₂ := eq105 X0 X1 X2
       grind)
    | exact superpose eq105 eq2627
    | (have j0 := eq2627 X0 X1 X2
       grind)
    | exact resolve eq2627 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq2627
  have eq2629 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2628 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq3086 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ (M.op X0 X0)) X1
       have i₂ := eq651 X0
       grind)
    | exact superpose eq651 eq21
    | exact resolve eq21 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3087 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ (M.op X0 X0))
       have i₂ := eq651 X0
       grind)
    | exact superpose eq651 eq31
    | exact resolve eq31 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq3137 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3086 (k X0 X0) X1
       have i₂ := eq761 X0 (k X0 X0)
       grind)
    | exact superpose eq761 eq3086
    | (have j1 := eq761 X0 X1
       grind)
    | exact resolve eq3086 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq3086
  have eq4202 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq3137 X0 X1
       grind)
    | exact superpose eq3137 eq31
    | (have j1 := eq3137 X0 X2
       grind)
    | exact resolve eq31 eq3137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3137
  have eq4687 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (σ (k X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq4202 X0 (σ (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4688 : ∀ X0 : G, (M.op X0 (σ (k X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq4687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4687
  have eq4843 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq232 (k X0 X0) X0
       have i₂ := eq4688 X0
       grind)
    | exact superpose eq4688 eq232
    | exact resolve eq232 eq4688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq4688
  have eq20367 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq1462 X0 X0 (σ (σ (k X0 X0)))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq20368 : ∀ X0 : G, (k X0 (σ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have j0 := eq20367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20367
  have eq20641 : ∀ X0 X1 : G, (τ (k X1 X0)) = (k (τ X1) (k (τ X0) (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq155 X0 (σ (k X0 X0)) X1
       have i₂ := eq20368 X0
       grind)
    | exact superpose eq20368 eq155
    | exact resolve eq155 eq20368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq29057 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq4843 (τ X0)
       have i₂ := eq1140 (τ X0) X0 (τ X0)
       grind)
    | exact superpose eq1140 eq4843
    | (have j1 := eq1140 (τ X0) X0 x
       grind)
    | exact resolve eq4843 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq4843
  have eq29108 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq29057 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29057
  have eq29143 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29108 X0
       have i₂ := eq38 (τ (τ X0)) (τ X0)
       grind)
    | exact superpose eq38 eq29108
    | (have j0 := eq29108 X0
       grind)
    | exact resolve eq29108 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq29108
  have eq29179 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq29143 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq29143 X0
       have r₂ := eq12 (τ X0) (τ X0)
       grind)
    | exact resolve eq29143 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29143
  have eq29194 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29179 X0
       have i₂ := eq154 X0 X0
       grind)
    | exact superpose eq154 eq29179
    | exact resolve eq29179 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq29179
  have eq29219 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29194 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29194
    | exact resolve eq29194 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29289 : ∀ X0 X1 : G, (k X1 (τ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (τ X0) X1
       have i₂ := eq29194 X0
       grind)
    | exact superpose eq29194 eq67
    | exact resolve eq67 eq29194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq29290 : ∀ X0 X1 : G, (k X1 (σ (τ (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108 X1 (τ X0)
       have i₂ := eq29194 X0
       grind)
    | exact superpose eq29194 eq108
    | exact resolve eq108 eq29194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq29194
  have eq29373 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq29290 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq29290
    | exact resolve eq29290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29290
  have eq29394 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq29219 X0
       have i₂ := eq107 (σ X0) X0
       grind)
    | exact superpose eq107 eq29219
    | exact resolve eq29219 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq29219
  have eq29412 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq29394 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29394
    | exact resolve eq29394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29394
  have eq30300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq29412 (σ X0)
       grind)
    | exact superpose eq29412 eq15
    | exact resolve eq15 eq29412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30373 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30300 X0
       have i₂ := eq29412 X0
       grind)
    | exact superpose eq29412 eq30300
    | exact resolve eq30300 eq29412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29412 eq30300
  have eq31468 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (σ (τ (k X1 X1)))) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (τ (k X1 X1)))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X0 (τ (k X1 X1)) X2
       have i₂ := eq29289 X1 (τ X0)
       grind)
    | exact superpose eq29289 eq173
    | (have j0 := eq173 X0 (τ (k X1 X1)) X2
       grind)
    | exact resolve eq173 eq29289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq29289
  have eq31522 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (k X0 (k X1 X1)) (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (τ (k X1 X1)))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31468 X0 X1 X2
       have i₂ := eq11 (k X1 X1)
       grind)
    | exact superpose eq11 eq31468
    | (have j0 := eq31468 X0 X1 X2
       grind)
    | exact resolve eq31468 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31468
  have eq31593 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (τ (k X1 X1)))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31522 X0 X1 X2
       have i₂ := eq29373 X1 X0
       grind)
    | exact superpose eq29373 eq31522
    | (have j0 := eq31522 X0 X1 X2
       grind)
    | exact resolve eq31522 eq29373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31522
  have eq31615 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (τ (k X1 X1)))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31593 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq31593
    | (have j0 := eq31593 X0 X1 X2
       grind)
    | exact resolve eq31593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31593
  have eq31618 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = (k X0 (k X1 X1)) ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31615 X0 X1 X2
       have i₂ := eq11 (k X1 X1)
       grind)
    | exact superpose eq11 eq31615
    | (have j0 := eq31615 X0 X1 X2
       grind)
    | exact resolve eq31615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31615
  have eq31620 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = X0 ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31618 X0 X1 X2
       have i₂ := eq29373 X1 X0
       grind)
    | exact superpose eq29373 eq31618
    | (have j0 := eq31618 X0 X1 X2
       grind)
    | exact resolve eq31618 eq29373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31618
  have eq31621 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = X0 ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ (τ (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31620 X0 X1 X2
       have i₂ := eq30373 X2
       grind)
    | exact superpose eq30373 eq31620
    | (have j0 := eq31620 X0 X1 X2
       grind)
    | exact resolve eq31620 eq30373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30373 eq31620
  have eq31622 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (k X1 X1))) ∨ (σ (M.op X2 X2)) = X0 ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31621 X0 X1 X2
       have i₂ := eq11 (k X1 X1)
       grind)
    | exact superpose eq11 eq31621
    | (have j0 := eq31621 X0 X1 X2
       grind)
    | exact resolve eq31621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31621
  have eq31623 : ∀ X0 X2 : G, (σ X2) = (M.op (σ X2) X0) ∨ (σ (M.op X2 X2)) = X0 ∨ (k X0 (σ X2)) = (M.op X0 (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq31622 X0 x X2
       have i₂ := eq29373 x X0
       grind)
    | exact superpose eq29373 eq31622
    | (have j0 := eq31622 X0 x X2
       grind)
    | exact resolve eq31622 eq29373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29373 eq31622
  have eq31624 : ∀ X0 X2 : G, (k X0 (σ X2)) = (M.op X0 (σ X2)) ∨ (σ (M.op X2 X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq31623 X0 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq31623 X0 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq31623 (M.op (σ (M.op X2 X2)) X0) X2
       have r₂ := eq12 X0 (σ (M.op X2 X2))
       grind)
    | exact resolve eq31623 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31623
  have eq125389 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (k X1 (σ (σ (k X1 X1))))) ∨ (σ (τ X0)) = (M.op (k X1 (σ (σ (k X1 X1)))) (k X1 (σ (σ (k X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2629 X1 (σ (k X1 X1)) (τ X0)
       have i₂ := eq20641 X1 X0
       grind)
    | exact superpose eq20641 eq2629
    | (have j0 := eq2629 X1 (σ (k X1 X1)) (τ X0)
       grind)
    | exact resolve eq2629 eq20641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629 eq20641
  have eq125410 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (M.op (k X1 (σ (σ (k X1 X1)))) (k X1 (σ (σ (k X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq125389 X0 X1
       have i₂ := eq20368 X1
       grind)
    | exact superpose eq20368 eq125389
    | (have j0 := eq125389 X0 X1
       grind)
    | exact resolve eq125389 eq20368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125389
  have eq125567 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (k X1 (σ (σ (k X1 X1)))) (k X1 (σ (σ (k X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq125410 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq125410
    | (have j0 := eq125410 X0 X1
       grind)
    | exact resolve eq125410 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125410
  have eq125624 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (M.op (k X1 (σ (σ (k X1 X1)))) (k X1 (σ (σ (k X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq125567 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq125567
    | (have j0 := eq125567 X0 X1
       grind)
    | exact resolve eq125567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125567
  have eq125662 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq125624 X0 X0
       have i₂ := eq20368 X0
       grind)
    | exact superpose eq20368 eq125624
    | (have j0 := eq125624 X0 X1
       grind)
    | exact resolve eq125624 eq20368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20368 eq125624
  have eq125679 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq125662 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq125662
    | (have j0 := eq125662 X0 X1
       grind)
    | exact resolve eq125662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125662
  have eq126334 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq125679 (τ X0) X1
       grind)
    | exact superpose eq125679 eq18
    | (have j1 := eq125679 (τ X0) X1
       grind)
    | exact resolve eq18 eq125679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq125679
  have eq154695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq31624 (σ X0) X1
       grind)
    | exact superpose eq31624 eq15
    | (have j1 := eq31624 (σ X0) X1
       grind)
    | exact resolve eq15 eq31624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31624
  have eq284866 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq126334 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq126334
    | exact resolve eq126334 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126334
  have eq285893 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq284866 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq284866
    | (have j0 := eq284866 X0 X1
       grind)
    | exact resolve eq284866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284866
  have eq633517 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq154695 x y
       grind)
    | exact superpose eq154695 eq16
    | (have j1 := eq154695 x y
       grind)
    | exact resolve eq16 eq154695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154695
  have eq635174 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq633517
       have i₂ := eq285893 x y
       grind)
    | exact superpose eq285893 eq633517
    | (have j1 := eq285893 x y
       grind)
    | (have r₁ := eq633517
       have r₂ := eq285893 x y
       grind)
    | exact resolve eq633517 eq285893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285893 eq633517
  have eq635178 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq635174
  have eq635204 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq635178
       grind)
    | exact superpose eq635178 eq31
    | exact resolve eq31 eq635178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635178
  have eq636412 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq635204 X0
       grind)
    | exact superpose eq635204 eq10
    | (have j1 := eq635204 X0
       grind)
    | exact resolve eq10 eq635204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635204
  have eq637182 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq636412 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq636412
    | (have j0 := eq636412 X0
       grind)
    | exact resolve eq636412 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636412
  have eq637887 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 y X0
       have i₂ := eq637182 X1
       grind)
    | exact superpose eq637182 eq21
    | (have j1 := eq637182 X1
       grind)
    | exact resolve eq21 eq637182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq637182
  have eq638119 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq637887 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637887
  have eq638120 : x = (M.op x x) := by grind
  clear eq638119
  have eq641625 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 x
       have i₂ := eq638120
       grind)
    | exact superpose eq638120 eq31
    | exact resolve eq31 eq638120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq641655 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq3087 x x
       have i₂ := eq638120
       grind)
    | exact superpose eq638120 eq3087
    | exact resolve eq3087 eq638120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087 eq638120
  have eq662995 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq641655 (σ y)
       grind)
    | exact superpose eq641655 eq16
    | exact resolve eq16 eq641655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641655
  have eq663336 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq662995
       have i₂ := eq641625 y
       grind)
    | exact superpose eq641625 eq662995
    | exact resolve eq662995 eq641625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641625 eq662995
  have eq663337 : False := by grind
  exact eq663337

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq37 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq169 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq175 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq169 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq169 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq169 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq169 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq860 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq175
  have eq888 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq860 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq1506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq888 (σ X0) (σ X1)
       grind)
    | exact superpose eq888 eq15
    | exact resolve eq15 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1506 X0 X1
       have i₂ := eq888 X0 X1
       grind)
    | exact superpose eq888 eq1506
    | exact resolve eq1506 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq1506
  have eq1532 : False := by grind
  exact eq1532

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_x_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (M.op X1 X1) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq38 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    grind
  have eq41 : ∀ X0 : G, (k (M.op X0 X0) X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  clear eq33
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq41
    | exact resolve eq41 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq68 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq20 X0 X1
       grind)
    | exact resolve eq13 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq119 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq120 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq128 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq160 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq120 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq120
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 (k (τ X0) X1) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq21
    | (have j1 := eq115 X0 X0
       grind)
    | exact resolve eq21 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq115 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq202 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq208 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq399 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (M.op X0 (σ X1)) (σ X2)) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 X0 X1 X2
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq119
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq202 (M.op X0 X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq202
    | (have j0 := eq202 (M.op X0 X0)
       grind)
    | exact resolve eq202 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq202
  have eq510 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq505 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq541 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ (M.op X0 X0))
       have i₂ := eq510 X0
       grind)
    | exact superpose eq510 eq31
    | exact resolve eq31 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq593 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq35 (M.op X1 X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq35
    | (have j1 := eq76 X0 X1
       grind)
    | exact resolve eq35 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq76
  have eq606 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq593 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq617 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq606 X1 (M.op X0 X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq606
    | exact resolve eq606 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq606 (M.op X1 X0) X0
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq606
    | exact resolve eq606 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq621 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq606 (M.op X1 X1) X0
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq606
    | exact resolve eq606 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq660 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 (M.op X1 X1)
       have i₂ := eq617 X1 (σ X0)
       grind)
    | exact superpose eq617 eq128
    | exact resolve eq128 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq617
  have eq668 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq660 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq660
    | exact resolve eq660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq683 : ∀ X0 X1 X2 : G, (M.op X1 (k (σ X0) (σ X0))) = X1 ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38 (σ X0) X1
       have i₂ := eq208 X0 X2
       grind)
    | exact superpose eq208 eq38
    | (have j1 := eq208 X0 X2
       grind)
    | exact resolve eq38 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq702 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq683 X0 X1 X2
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq683
    | (have j0 := eq683 X0 X1 X1
       grind)
    | exact resolve eq683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq980 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120 (M.op X0 X0) X1
       have i₂ := eq621 (σ X1) X0
       grind)
    | exact superpose eq621 eq120
    | exact resolve eq120 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1820 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ X0)) X1) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq980 (σ X0) X1
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq980
    | (have j1 := eq208 X0 X2
       grind)
    | exact resolve eq980 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq1864 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1820 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1820
    | (have j0 := eq1820 X0 X1 X2
       grind)
    | exact resolve eq1820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq2088 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq184 X0 X1 X2
       grind)
    | exact superpose eq184 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq184 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq184 X0 X1 X2
       grind)
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2091 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2088 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2092 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2091 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2093 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (k (k (τ X0) X1) X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2092 X0 X1 X2
       have i₂ := eq119 X0 X1 X2
       grind)
    | exact superpose eq119 eq2092
    | (have j0 := eq2092 X0 X1 X2
       grind)
    | exact resolve eq2092 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq2092
  have eq4701 : ∀ X0 X1 X2 : G, (k X1 (τ (σ (k X0 X0)))) = X1 ∨ (k X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq668 X1 (σ (k X0 X0))
       have i₂ := eq1864 X0 X2 (σ (k X0 X0))
       grind)
    | exact superpose eq1864 eq668
    | (have j1 := eq1864 X1 (τ (σ (k X0 X0))) X2
       grind)
    | exact resolve eq668 eq1864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq1864
  have eq4737 : ∀ X0 X1 X2 : G, (k X1 (k X0 X0)) = X1 ∨ (k X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4701 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4701
    | (have j0 := eq4701 X1 X1 (k X0 X0)
       grind)
    | exact resolve eq4701 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701
  have eq4812 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4737 X0 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737
  have eq4813 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq4812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4812
  have eq6197 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 (σ (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq702 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq6198 : ∀ X0 X1 : G, (M.op X0 (σ (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq6197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6197
  have eq6278 : ∀ X0 X1 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq980 (σ (k X1 X1)) X1
       have i₂ := eq6198 (σ (k X1 X1)) X1
       grind)
    | exact superpose eq6198 eq980
    | exact resolve eq980 eq6198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq6300 : ∀ X0 X1 : G, (k X0 (σ (k X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq620 (σ (k X1 X1)) X0
       have i₂ := eq6198 X0 X1
       grind)
    | exact superpose eq6198 eq620
    | exact resolve eq620 eq6198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq6198
  have eq6310 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6278 X0 X1
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq6278
    | exact resolve eq6278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278
  have eq35128 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq621 (σ X1) (σ X0)
       have i₂ := eq399 (σ X0) X0 X1
       grind)
    | exact superpose eq399 eq621
    | (have j1 := eq399 (σ X0) X0 x
       grind)
    | exact resolve eq621 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq621
  have eq35170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k (k (τ (σ X0)) X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq35128 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35128
  have eq35207 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq35170 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq35170
    | (have j0 := eq35170 X0 X1
       grind)
    | exact resolve eq35170 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35170
  have eq35296 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35207 X0 x
       have i₂ := eq6310 X0 x
       grind)
    | exact superpose eq6310 eq35207
    | (have j0 := eq35207 X0 x
       grind)
    | exact resolve eq35207 eq6310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6310 eq35207
  have eq73120 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2093 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093
  have eq73121 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq73120 X0 X1 X2
       have j1 := eq184 X0 X1 X2
       grind)
    | (have r₁ := eq73120 X0 X1 X2
       have r₂ := eq184 X0 X1 X2
       grind)
    | exact resolve eq73120 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq73120
  have eq191306 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq35296
  have eq191469 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq191306 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq191306
    | (have j0 := eq191306 X0
       grind)
    | exact resolve eq191306 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191306
  have eq191470 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq191469 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191469
  have eq191502 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq191470 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191470
    | exact resolve eq191470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192183 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq191502 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq191502
    | exact resolve eq191502 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq191502
  have eq192287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq192183 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq192183
    | exact resolve eq192183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192183
  have eq194625 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq160 X0 X0
       have i₂ := eq192287 (τ X0)
       grind)
    | exact superpose eq192287 eq160
    | exact resolve eq160 eq192287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq194741 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq194625 X0
       have i₂ := eq192287 X0
       grind)
    | exact superpose eq192287 eq194625
    | exact resolve eq194625 eq192287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194625
  have eq300012 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (k X0 (σ (k (τ X0) (τ X0)))) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq73121 X0 (k (τ X0) (τ X0)) X1
       have i₂ := eq4813 (τ X0)
       grind)
    | exact superpose eq4813 eq73121
    | (have j0 := eq73121 X0 (k (τ X0) (τ X0)) X1
       grind)
    | exact resolve eq73121 eq4813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4813 eq73121
  have eq301251 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq300012 X0 X1
       have i₂ := eq6300 X0 (τ X0)
       grind)
    | exact superpose eq6300 eq300012
    | (have j0 := eq300012 X0 X1
       grind)
    | exact resolve eq300012 eq6300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300012
  have eq301793 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq301251 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq301251
    | (have j0 := eq301251 X0 X1
       grind)
    | exact resolve eq301251 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301251
  have eq302148 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq301793 X0 X1
       have i₂ := eq6300 X0 (τ X0)
       grind)
    | exact superpose eq6300 eq301793
    | (have j0 := eq301793 X0 X1
       grind)
    | exact resolve eq301793 eq6300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6300 eq301793
  have eq302437 : ∀ X0 X1 : G, (σ (k X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq302148 X0 X1
       have i₂ := eq191470 X1
       grind)
    | exact superpose eq191470 eq302148
    | (have j0 := eq302148 X0 X1
       grind)
    | exact resolve eq302148 eq191470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191470 eq302148
  have eq302669 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq302437 X0 X1
       have i₂ := eq192287 X1
       grind)
    | exact superpose eq192287 eq302437
    | (have j0 := eq302437 X0 X1
       grind)
    | exact resolve eq302437 eq192287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192287 eq302437
  have eq303094 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq302669 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302669
    | (have j0 := eq302669 X1 (τ X0)
       grind)
    | exact resolve eq302669 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303681 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq302669 (σ X0) X1
       grind)
    | exact superpose eq302669 eq15
    | (have j1 := eq302669 (σ X0) X1
       grind)
    | exact resolve eq15 eq302669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302669
  have eq303937 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq303094 X0 X1
       have i₂ := eq194741 X0
       grind)
    | exact superpose eq194741 eq303094
    | (have j0 := eq303094 X0 X1
       grind)
    | exact resolve eq303094 eq194741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194741 eq303094
  have eq303996 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq303937 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq303937
    | (have j0 := eq303937 X0 X1
       grind)
    | exact resolve eq303937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303937
  have eq304917 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq303996 X1 (τ X0)
       grind)
    | exact superpose eq303996 eq18
    | (have j1 := eq303996 X1 (τ X0)
       grind)
    | exact resolve eq18 eq303996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq303996
  have eq319878 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304917 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq304917
    | exact resolve eq304917 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304917
  have eq320754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq319878 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq319878
    | (have j0 := eq319878 X0 X1
       grind)
    | exact resolve eq319878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319878
  have eq358292 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq303681 x y
       grind)
    | exact superpose eq303681 eq16
    | (have j1 := eq303681 x y
       grind)
    | exact resolve eq16 eq303681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303681
  have eq359048 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq358292
       have i₂ := eq320754 x y
       grind)
    | exact superpose eq320754 eq358292
    | (have j1 := eq320754 x y
       grind)
    | (have r₁ := eq358292
       have r₂ := eq320754 x y
       grind)
    | exact resolve eq358292 eq320754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320754 eq358292
  have eq359051 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq359048
  have eq359838 : ∀ X0 : G, (σ x) = (σ (M.op y y)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 y
       have i₂ := eq359051
       grind)
    | exact superpose eq359051 eq31
    | exact resolve eq31 eq359051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359051
  have eq360853 : ∀ X0 : G, (M.op y y) = (τ (σ x)) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq359838 X0
       grind)
    | exact superpose eq359838 eq10
    | (have j1 := eq359838 X0
       grind)
    | exact resolve eq10 eq359838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359838
  have eq361273 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq360853 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq360853
    | (have j0 := eq360853 X0
       grind)
    | exact resolve eq360853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360853
  have eq361524 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ x = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq21 y X0
       have i₂ := eq361273 X1
       grind)
    | exact superpose eq361273 eq21
    | (have j1 := eq361273 X1
       grind)
    | exact resolve eq21 eq361273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq361273
  have eq362001 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq361524 x x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361524
  have eq362002 : x = (M.op x x) := by grind
  clear eq362001
  have eq362010 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq31 X0 x
       have i₂ := eq362002
       grind)
    | exact superpose eq362002 eq31
    | exact resolve eq31 eq362002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq362044 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq541 x x
       have i₂ := eq362002
       grind)
    | exact superpose eq362002 eq541
    | exact resolve eq541 eq362002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq362002
  have eq368240 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq362044 (σ y)
       grind)
    | exact superpose eq362044 eq16
    | exact resolve eq16 eq362044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362044
  have eq368511 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq368240
       have i₂ := eq362010 y
       grind)
    | exact superpose eq362010 eq368240
    | exact resolve eq368240 eq362010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362010 eq368240
  have eq368512 : False := by grind
  exact eq368512

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y x
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ y) (σ x)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X0) X0
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq50 eq47
    | exact resolve eq47 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq48 (M.op X1 X1) X0
       grind)
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq90 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq125 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq585 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq590 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq592 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq591 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq594 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq585 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq600 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq594 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq594
    | (have j0 := eq594 X0
       grind)
    | exact resolve eq594 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq2947 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq592 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq592
    | (have j0 := eq592 (τ X0)
       grind)
    | exact resolve eq592 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq2956 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2947 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2947
    | (have j0 := eq2947 X0
       grind)
    | exact resolve eq2947 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq2962 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2956 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2956
    | (have j0 := eq2956 X0
       grind)
    | exact resolve eq2956 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956
  have eq3285 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (k (τ X0) (τ X0))
       have i₂ := eq600 (τ X0)
       grind)
    | exact superpose eq600 eq39
    | (have j1 := eq600 (τ X0)
       grind)
    | exact resolve eq39 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq600
  have eq3328 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3285 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq3285
    | (have j0 := eq3285 X0
       grind)
    | exact resolve eq3285 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3285
  have eq3341 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3328 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3328
    | (have j0 := eq3328 X0
       grind)
    | exact resolve eq3328 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq3352 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3341 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3341
    | (have j0 := eq3341 X0
       grind)
    | exact resolve eq3341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341
  have eq8881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq8882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8881
    | exact resolve eq8881 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8881
  have eq8893 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8882
       have r₂ := eq28
       grind)
    | exact resolve eq8882 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8882
  have eq8895 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8893
    | exact resolve eq8893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8893
  have eq8900 : ∀ X0 : G, x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq8895 eq48
    | exact resolve eq48 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8904 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8895 eq52
    | exact resolve eq52 eq8895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895
  have eq8907 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8904
    | exact resolve eq8904 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8904
  have eq9019 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq67 y
       have i₂ := eq8907
       grind)
    | exact superpose eq8907 eq67
    | exact resolve eq67 eq8907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9025 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq8907
       grind)
    | exact superpose eq8907 eq52
    | exact resolve eq52 eq8907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8907
  have eq9028 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9025
    | exact resolve eq9025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9025
  have eq9031 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9028 eq56
    | exact resolve eq56 eq9028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq9028
  have eq9161 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq590 x x
       have i₂ := eq9019
       grind)
    | exact superpose eq9019 eq590
    | (have j0 := eq590 x x
       grind)
    | exact resolve eq590 eq9019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9019
  have eq9164 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9161
  have eq9165 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9164
  have eq9174 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9165
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9165
    | exact resolve eq9165 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9165
  have eq9484 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9031 eq48
    | exact resolve eq48 eq9031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9031
  have eq9716 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9174 eq65
    | exact resolve eq65 eq9174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9174
  have eq10184 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9484 eq27
    | (have j1 := eq9484 (σ x)
       grind)
    | exact resolve eq27 eq9484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9484
  have eq10187 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq10184
  have eq10539 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9716 eq27
    | (have j1 := eq9716 (σ y)
       grind)
    | exact resolve eq27 eq9716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9716
  have eq10556 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10539
  have eq10559 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10556 eq50
    | exact resolve eq50 eq10556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10556
  have eq10681 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10559 eq48
    | exact resolve eq48 eq10559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10559
  have eq10907 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10681 eq27
    | (have j1 := eq10681 (σ x)
       grind)
    | exact resolve eq27 eq10681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10681
  have eq10910 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10907
  have eq10917 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10910 eq28
    | exact resolve eq28 eq10910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10910
  have eq11763 : ∀ X0 : G, x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y y
       have i₂ := eq8900 X0
       grind)
    | exact superpose eq8900 eq52
    | (have j1 := eq8900 X0
       grind)
    | exact resolve eq52 eq8900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8900
  have eq11766 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11763 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11763
    | (have j0 := eq11763 X0
       grind)
    | exact resolve eq11763 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11763
  have eq11770 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11766 eq67
    | exact resolve eq67 eq11766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11766
  have eq11787 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11770 eq90
    | exact resolve eq90 eq11770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq11770
  have eq11825 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11787
    | exact resolve eq11787 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11787
  have eq12098 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq11825
       grind)
    | exact superpose eq11825 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq11825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11825
  have eq12099 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12098
  have eq12128 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65 X0 x
       have i₂ := eq12099
       grind)
    | exact superpose eq12099 eq65
    | exact resolve eq65 eq12099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq12099
  have eq12370 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq12128 y
       grind)
    | exact superpose eq12128 eq19
    | (have j1 := eq12128 y
       grind)
    | exact resolve eq19 eq12128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12128
  have eq12387 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12370
  have eq12393 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12387 eq50
    | exact resolve eq50 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq12397 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12387 eq10187
    | exact resolve eq10187 eq12387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10187 eq12387
  have eq12400 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12397
  have eq12407 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12400 eq30
    | exact resolve eq30 eq12400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12400
  have eq12567 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq12407
    | exact resolve eq12407 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12407
  have eq12580 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12567 eq49
    | exact resolve eq49 eq12567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq12567
  have eq12978 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12393 eq67
    | exact resolve eq67 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq13424 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12978 eq125
    | exact resolve eq125 eq12978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq12978
  have eq13464 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq13424
    | exact resolve eq13424 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13424
  have eq13759 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq48 y X0
       have i₂ := eq12580
       grind)
    | exact superpose eq12580 eq48
    | exact resolve eq48 eq12580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq12580
  have eq14489 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq13759 x
       grind)
    | exact superpose eq13759 eq19
    | (have j1 := eq13759 x
       grind)
    | exact resolve eq19 eq13759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13759
  have eq14494 : x = (M.op x y) ∨ x = y := by grind
  clear eq14489
  have eq14501 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14494 eq21
    | exact resolve eq21 eq14494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14628 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14501
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14501
    | exact resolve eq14501 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14501
  have eq14701 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14628 eq10917
    | (have r₁ := eq10917
       have r₂ := eq14628
       grind)
    | exact resolve eq10917 eq14628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10917 eq14628
  have eq14716 : y = (M.op x y) ∨ x = y := by grind
  clear eq14701
  have eq14845 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14716 eq14494
    | exact resolve eq14494 eq14716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14494 eq14716
  have eq14846 : x = y := by grind
  clear eq14845
  have eq14913 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14846
       grind)
    | exact superpose eq14846 eq19
    | exact resolve eq19 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14914 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq14846
       grind)
    | exact superpose eq14846 eq25
    | exact resolve eq25 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq15041 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14914
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14914
    | exact resolve eq14914 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14914
  have eq15043 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15041 eq27
    | exact resolve eq27 eq15041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15041
  have eq15556 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq14913
       grind)
    | exact superpose eq14913 eq67
    | exact resolve eq67 eq14913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq16015 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15556 eq590
    | (have j0 := eq590 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq590 eq15556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq15556
  have eq16018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq16015
  have eq16019 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq16018
  have eq16026 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16019
    | exact resolve eq16019 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16019
  have eq19095 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3352 y
       have i₂ := eq13464
       grind)
    | exact superpose eq13464 eq3352
    | (have j0 := eq3352 y
       grind)
    | exact resolve eq3352 eq13464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq13464
  have eq19171 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq2962 y
       grind)
    | (have r₁ := eq19095
       have r₂ := eq2962 y
       grind)
    | exact resolve eq19095 eq2962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962 eq19095
  have eq19200 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19171
       have i₂ := eq14846
       grind)
    | exact superpose eq14846 eq19171
    | exact resolve eq19171 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19171
  have eq19217 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19200
       have i₂ := eq14913
       grind)
    | exact superpose eq14913 eq19200
    | exact resolve eq19200 eq14913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14913 eq19200
  have eq19218 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19217
  have eq19235 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19218
       have i₂ := eq14846
       grind)
    | exact superpose eq14846 eq19218
    | exact resolve eq19218 eq14846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846 eq19218
  have eq19236 : x = (M.op x y) := by grind
  clear eq19235
  have eq19243 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq19236 eq21
    | exact resolve eq21 eq19236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq19236
  have eq19386 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19243
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19243
    | exact resolve eq19243 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq19243
  have eq19584 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19386 eq15043
    | exact resolve eq15043 eq19386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15043 eq19386
  have eq19591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16026 eq19584
    | exact resolve eq19584 eq16026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16026 eq19584
  have eq19659 : False := by grind
  exact eq19659

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y x
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (σ y) (σ x)
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X1 X0) X0
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq50 eq47
    | exact resolve eq47 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq48 (M.op X1 X1) X0
       grind)
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq83 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq90
    | exact resolve eq90 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq118 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq425 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq429 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq431 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq433 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq425 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq438 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq433
    | (have j0 := eq433 X0
       grind)
    | exact resolve eq433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq2940 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq431 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq431
    | (have j0 := eq431 (τ X0)
       grind)
    | exact resolve eq431 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq2949 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2940 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2940
    | (have j0 := eq2940 X0
       grind)
    | exact resolve eq2940 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2940
  have eq2955 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2949 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2949
    | (have j0 := eq2949 X0
       grind)
    | exact resolve eq2949 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2949
  have eq3122 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0 (k (τ X0) (τ X0))
       have i₂ := eq438 (τ X0)
       grind)
    | exact superpose eq438 eq39
    | (have j1 := eq438 (τ X0)
       grind)
    | exact resolve eq39 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq438
  have eq3165 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3122 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq3122
    | (have j0 := eq3122 X0
       grind)
    | exact resolve eq3122 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3122
  have eq3178 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3165 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3165
    | (have j0 := eq3165 X0
       grind)
    | exact resolve eq3165 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165
  have eq3189 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3178 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3178
    | (have j0 := eq3178 X0
       grind)
    | exact resolve eq3178 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3178
  have eq8329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq8330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8329
    | exact resolve eq8329 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq8341 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8330
       have r₂ := eq28
       grind)
    | exact resolve eq8330 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8330
  have eq8343 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8341
    | exact resolve eq8341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8341
  have eq8348 : ∀ X0 : G, x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq8343 eq48
    | exact resolve eq48 eq8343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8352 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8343 eq52
    | exact resolve eq52 eq8343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8343
  have eq8355 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq8352
    | exact resolve eq8352 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8352
  have eq8357 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq71 y
       have i₂ := eq8355
       grind)
    | exact superpose eq8355 eq71
    | exact resolve eq71 eq8355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8363 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq8355
       grind)
    | exact superpose eq8355 eq52
    | exact resolve eq52 eq8355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8355
  have eq8366 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8363
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8363
    | exact resolve eq8363 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8363
  have eq8478 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8366 eq56
    | exact resolve eq56 eq8366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq8366
  have eq8606 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq429 x x
       have i₂ := eq8357
       grind)
    | exact superpose eq8357 eq429
    | (have j0 := eq429 x x
       grind)
    | exact resolve eq429 eq8357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8357
  have eq8609 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8606
  have eq8610 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8609
  have eq8617 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8610
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8610
    | exact resolve eq8610 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8610
  have eq8812 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8478 eq48
    | exact resolve eq48 eq8478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8478
  have eq9147 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8617 eq69
    | exact resolve eq69 eq8617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8617
  have eq9605 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8812 eq27
    | (have j1 := eq8812 (σ x)
       grind)
    | exact resolve eq27 eq8812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8812
  have eq9608 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq9605
  have eq9846 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9147 eq27
    | (have j1 := eq9147 (σ y)
       grind)
    | exact resolve eq27 eq9147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9147
  have eq9863 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq9846
  have eq9866 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9863 eq50
    | exact resolve eq50 eq9863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9863
  have eq10097 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq9866 eq48
    | exact resolve eq48 eq9866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9866
  have eq10210 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10097 eq27
    | (have j1 := eq10097 (σ x)
       grind)
    | exact resolve eq27 eq10097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10097
  have eq10213 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10210
  have eq10328 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10213 eq28
    | exact resolve eq28 eq10213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10213
  have eq11022 : ∀ X0 : G, x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y y
       have i₂ := eq8348 X0
       grind)
    | exact superpose eq8348 eq52
    | (have j1 := eq8348 X0
       grind)
    | exact resolve eq52 eq8348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8348
  have eq11025 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11022 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11022
    | (have j0 := eq11022 X0
       grind)
    | exact resolve eq11022 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11022
  have eq11029 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11025 eq71
    | exact resolve eq71 eq11025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11025
  have eq11046 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11029 eq83
    | exact resolve eq83 eq11029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq11029
  have eq11081 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq11046
    | exact resolve eq11046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq11338 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq11081
       grind)
    | exact superpose eq11081 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq11081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11081
  have eq11339 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11338
  have eq11365 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq69 X0 x
       have i₂ := eq11339
       grind)
    | exact superpose eq11339 eq69
    | exact resolve eq69 eq11339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq11339
  have eq11589 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq11365 y
       grind)
    | exact superpose eq11365 eq19
    | (have j1 := eq11365 y
       grind)
    | exact resolve eq19 eq11365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11365
  have eq11606 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11589
  have eq11612 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11606 eq50
    | exact resolve eq50 eq11606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq11616 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11606 eq9608
    | exact resolve eq9608 eq11606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9608 eq11606
  have eq11619 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11616
  have eq11733 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11619 eq30
    | exact resolve eq30 eq11619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11619
  have eq11893 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq11733
    | exact resolve eq11733 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11733
  have eq12006 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq11893 eq49
    | exact resolve eq49 eq11893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11893
  have eq12393 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11612 eq71
    | exact resolve eq71 eq11612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11612
  have eq12705 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12393 eq118
    | exact resolve eq118 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq12393
  have eq12742 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq12705
    | exact resolve eq12705 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12705
  have eq13021 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq48 y X0
       have i₂ := eq12006
       grind)
    | exact superpose eq12006 eq48
    | exact resolve eq48 eq12006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq12006
  have eq13723 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19
       have i₂ := eq13021 x
       grind)
    | exact superpose eq13021 eq19
    | (have j1 := eq13021 x
       grind)
    | exact resolve eq19 eq13021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13021
  have eq13728 : x = (M.op x y) ∨ x = y := by grind
  clear eq13723
  have eq13735 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq13728 eq21
    | exact resolve eq21 eq13728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13862 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq13735
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13735
    | exact resolve eq13735 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13735
  have eq13935 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13862 eq10328
    | (have r₁ := eq10328
       have r₂ := eq13862
       grind)
    | exact resolve eq10328 eq13862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10328 eq13862
  have eq13950 : y = (M.op x y) ∨ x = y := by grind
  clear eq13935
  have eq14079 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13950 eq13728
    | exact resolve eq13728 eq13950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13728 eq13950
  have eq14080 : x = y := by grind
  clear eq14079
  have eq14147 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq19
    | exact resolve eq19 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq14148 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq25
    | exact resolve eq25 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq14275 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14148
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14148
    | exact resolve eq14148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14148
  have eq14277 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14275 eq27
    | exact resolve eq27 eq14275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq14275
  have eq14445 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq71 x
       have i₂ := eq14147
       grind)
    | exact superpose eq14147 eq71
    | exact resolve eq71 eq14147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq14902 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14445 eq429
    | (have j0 := eq429 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq429 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq14445
  have eq14905 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq14902
  have eq14906 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq14905
  have eq14911 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq14906
    | exact resolve eq14906 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14906
  have eq18469 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3189 y
       have i₂ := eq12742
       grind)
    | exact superpose eq12742 eq3189
    | (have j0 := eq3189 y
       grind)
    | exact resolve eq3189 eq12742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3189 eq12742
  have eq18544 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq2955 y
       grind)
    | (have r₁ := eq18469
       have r₂ := eq2955 y
       grind)
    | exact resolve eq18469 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955 eq18469
  have eq18572 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18544
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq18544
    | exact resolve eq18544 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18544
  have eq18589 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18572
       have i₂ := eq14147
       grind)
    | exact superpose eq14147 eq18572
    | exact resolve eq18572 eq14147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14147 eq18572
  have eq18590 : x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18589
  have eq18607 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18590
       have i₂ := eq14080
       grind)
    | exact superpose eq14080 eq18590
    | exact resolve eq18590 eq14080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080 eq18590
  have eq18608 : x = (M.op x y) := by grind
  clear eq18607
  have eq18615 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18608 eq21
    | exact resolve eq21 eq18608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq18608
  have eq18758 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18615
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18615
    | exact resolve eq18615 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq18615
  have eq18956 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq18758 eq14277
    | exact resolve eq14277 eq18758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14277 eq18758
  have eq18963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14911 eq18956
    | exact resolve eq18956 eq14911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14911 eq18956
  have eq19031 : False := by grind
  exact eq19031

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxx_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq14 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ y) (σ x)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X1) X0 X1
       have i₂ := eq52 (M.op X1 X1) X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq74
    | exact resolve eq74 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq680 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq681 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq2922 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq681 (M.op X0 X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq681
    | (have j0 := eq681 (M.op X0 X0)
       grind)
    | exact resolve eq681 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq681
  have eq2930 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq2922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq15828 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ (M.op X0 X0))
       have i₂ := eq2930 X0
       grind)
    | exact superpose eq2930 eq73
    | exact resolve eq73 eq2930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2930
  have eq16660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq16661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16660
    | exact resolve eq16660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16660
  have eq16672 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16661
       have r₂ := eq28
       grind)
    | exact resolve eq16661 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16661
  have eq16677 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16672 eq52
    | exact resolve eq52 eq16672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16691 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16672 eq56
    | exact resolve eq56 eq16672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16672
  have eq16694 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16691
    | exact resolve eq16691 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16691
  have eq16698 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16694 eq56
    | exact resolve eq56 eq16694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16694
  have eq16711 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16698 eq73
    | exact resolve eq73 eq16698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16698
  have eq19205 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16711 eq27
    | (have j1 := eq16711 (σ y)
       grind)
    | exact resolve eq27 eq16711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16711
  have eq19239 : x = (M.op y y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19205
  have eq19253 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15828 y x
       have i₂ := eq19239
       grind)
    | exact superpose eq19239 eq15828
    | exact resolve eq15828 eq19239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19239
  have eq19265 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19253 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19253
    | (have j0 := eq19253 X0
       grind)
    | exact resolve eq19253 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19253
  have eq19581 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19265 eq27
    | (have j1 := eq19265 (σ y)
       grind)
    | exact resolve eq27 eq19265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19265
  have eq19615 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19581
  have eq19620 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19615
       grind)
    | exact superpose eq19615 eq56
    | exact resolve eq56 eq19615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19722 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq19620
       grind)
    | exact superpose eq19620 eq52
    | exact resolve eq52 eq19620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq19731 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15828 x x
       have i₂ := eq19620
       grind)
    | exact superpose eq19620 eq15828
    | exact resolve eq15828 eq19620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15828 eq19620
  have eq19742 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19731 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19731
    | (have j0 := eq19731 X0
       grind)
    | exact resolve eq19731 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19731
  have eq20029 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19615
       have i₂ := eq19722 y
       grind)
    | exact superpose eq19722 eq19615
    | exact resolve eq19615 eq19722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19615 eq19722
  have eq20038 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq20029
  have eq20054 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq20038 eq28
    | exact resolve eq28 eq20038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20038
  have eq20684 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19742 eq27
    | (have j1 := eq19742 (σ y)
       grind)
    | exact resolve eq27 eq19742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq19742
  have eq20718 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20684
  have eq20979 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq20718 eq28
    | exact resolve eq28 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq20980 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20718 eq54
    | exact resolve eq54 eq20718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq20718
  have eq38826 : ∀ X0 : G, x = (M.op y y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20980 eq16677
    | (have j0 := eq16677 X0
       grind)
    | exact resolve eq16677 eq20980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16677
  have eq38844 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 y y
       have i₂ := eq38826 X0
       grind)
    | exact superpose eq38826 eq56
    | (have j1 := eq38826 X0
       grind)
    | exact resolve eq56 eq38826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38826
  have eq38847 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq38844 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38844
    | (have j0 := eq38844 X0
       grind)
    | exact resolve eq38844 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38844
  have eq38862 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 x y
       have i₂ := eq38847 X0
       grind)
    | exact superpose eq38847 eq56
    | (have j1 := eq38847 X0
       grind)
    | exact resolve eq56 eq38847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq38847
  have eq38876 : ∀ X0 X1 : G, x = (M.op x X0) ∨ (M.op X1 (σ x)) = X1 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 x
       have i₂ := eq38862 X0
       grind)
    | exact superpose eq38862 eq73
    | (have j1 := eq38862 X1
       grind)
    | exact resolve eq73 eq38862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38862
  have eq38987 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq19
       have i₂ := eq38876 y X0
       grind)
    | exact superpose eq38876 eq19
    | (have j1 := eq38876 y X0
       grind)
    | exact resolve eq19 eq38876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38876
  have eq39024 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq38987 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38987
  have eq39047 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39024 eq71
    | exact resolve eq71 eq39024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39024
  have eq39079 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39047 eq50
    | exact resolve eq50 eq39047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39047
  have eq39124 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq39079
    | exact resolve eq39079 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39079
  have eq39190 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq39124
       grind)
    | exact superpose eq39124 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq39124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39124
  have eq39191 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq39190
  have eq39226 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq73 X0 x
       have i₂ := eq39191
       grind)
    | exact superpose eq39191 eq73
    | exact resolve eq73 eq39191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq39191
  have eq39298 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq39226 y
       grind)
    | exact superpose eq39226 eq19
    | (have j1 := eq39226 y
       grind)
    | exact resolve eq19 eq39226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39226
  have eq39333 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq39298
  have eq39597 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39333 eq30
    | exact resolve eq30 eq39333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39333
  have eq39756 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq39597
    | exact resolve eq39597 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39597
  have eq39758 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39756 eq21
    | exact resolve eq21 eq39756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39756
  have eq39973 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39758
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39758
    | exact resolve eq39758 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39758
  have eq39974 : x = y := by
    first
    | (have r₁ := eq39973
       have r₂ := eq20054
       grind)
    | exact resolve eq39973 eq20054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20054 eq39973
  have eq40222 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq39974
       grind)
    | exact superpose eq39974 eq19
    | exact resolve eq19 eq39974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40223 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39974
       grind)
    | exact superpose eq39974 eq25
    | exact resolve eq25 eq39974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39974
  have eq40445 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40223
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40223
    | exact resolve eq40223 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40223
  have eq40529 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40445 eq20980
    | exact resolve eq20980 eq40445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20980 eq40445
  have eq41093 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq40529 eq71
    | exact resolve eq71 eq40529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq40529
  have eq41749 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq41093 eq50
    | exact resolve eq50 eq41093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq41093
  have eq41796 : x = (k x x) := by
    first
    | exact superpose eq29 eq41749
    | exact resolve eq41749 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq41749
  have eq43554 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq41796
       grind)
    | exact superpose eq41796 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq41796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41796
  have eq43555 : x = (M.op x x) := by grind
  clear eq43554
  have eq43564 : x = (M.op x y) := by
    first
    | (have i₁ := eq43555
       have i₂ := eq40222
       grind)
    | exact superpose eq40222 eq43555
    | exact resolve eq43555 eq40222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40222 eq43555
  have eq43600 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq43564 eq21
    | exact resolve eq21 eq43564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq43564
  have eq43832 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq43600
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43600
    | exact resolve eq43600 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43600
  have eq43910 : False := by grind
  exact eq43910
