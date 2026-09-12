import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_x_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X0 X1 X3
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X2 X3 : G, (k X2 X3) = (M.op X2 X3) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq528 x x X2 X3
       grind)
    | (have r₁ := eq528 x x X2 X3
       have r₂ := eq56 x x X2
       grind)
    | exact resolve eq528 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq528
  have eq1373 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq536 x y
       grind)
    | exact superpose eq536 eq49
    | (have j1 := eq536 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1395 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1373
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1373
    | exact resolve eq1373 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1396 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq1395
    | exact resolve eq1395 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1396 eq536
    | (have j0 := eq536 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq536 eq1396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq1396
  have eq1409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1402
    | exact resolve eq1402 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402
  have eq1418 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1409
       have r₂ := eq28
       grind)
    | exact resolve eq1409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1424 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1418 eq30
    | exact resolve eq30 eq1418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1418
  have eq1442 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1424
    | exact resolve eq1424 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1424
  have eq1443 : x = y := by grind
  clear eq1442
  have eq1446 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq19
    | exact resolve eq19 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1447 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1443
       grind)
    | exact superpose eq1443 eq25
    | exact resolve eq25 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1443
  have eq1463 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1447
    | exact resolve eq1447 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1447
  have eq1466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1463 eq27
    | exact resolve eq27 eq1463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1463
  have eq1535 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1466 eq68
    | exact resolve eq68 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1466
  have eq1565 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1535
       have i₂ := eq1446
       grind)
    | exact superpose eq1446 eq1535
    | exact resolve eq1535 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446 eq1535
  have eq1566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1565 eq15
    | exact resolve eq15 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1566
    | exact resolve eq1566 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1566
  have eq1590 : False := by grind
  exact eq1590

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxx_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq94 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq540 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq56 X0 X1 X3
       grind)
    | exact superpose eq56 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | exact resolve eq12 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq540 x x X2 X3
       grind)
    | (have r₁ := eq540 x x X2 X3
       have r₂ := eq56 x x X2
       grind)
    | exact resolve eq540 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq540
  have eq1201 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq548 y x
       grind)
    | exact superpose eq548 eq94
    | (have j1 := eq548 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq94 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1221 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1201
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1201
    | exact resolve eq1201 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1222 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq1221
    | exact resolve eq1221 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1222 eq548
    | (have j0 := eq548 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq548 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq1222
  have eq1228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1226
    | exact resolve eq1226 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1231 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1228
       have r₂ := eq28
       grind)
    | exact resolve eq1228 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1234 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1231 eq30
    | exact resolve eq30 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1231
  have eq1252 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1234
    | exact resolve eq1234 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1234
  have eq1253 : x = y := by grind
  clear eq1252
  have eq1256 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq19
    | exact resolve eq19 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1257 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1253
       grind)
    | exact superpose eq1253 eq25
    | exact resolve eq25 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1253
  have eq1273 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1257
    | exact resolve eq1257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1257
  have eq1276 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1273 eq27
    | exact resolve eq27 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1273
  have eq1339 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1276 eq68
    | exact resolve eq68 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1276
  have eq1367 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1339
       have i₂ := eq1256
       grind)
    | exact superpose eq1256 eq1339
    | exact resolve eq1339 eq1256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256 eq1339
  have eq1369 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1367 eq15
    | exact resolve eq15 eq1367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1369
    | exact resolve eq1369 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1369
  have eq1393 : False := by grind
  exact eq1393

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq201 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq206 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq208 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq206
    | (have j0 := eq206 X0 X1
       grind)
    | exact resolve eq206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq212 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq208 X0 X1
       have j1 := eq204 X0 X1
       grind)
    | (have r₁ := eq208 X0 X1
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq208 X0 (k X1 X0)
       have r₂ := eq204 X0 X1
       grind)
    | (have r₁ := eq208 X0 X0
       have r₂ := eq204 X0 X0
       grind)
    | exact resolve eq208 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq208
  have eq541 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq212 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq212 x y
       grind)
    | exact superpose eq212 eq16
    | (have j1 := eq212 x y
       grind)
    | exact resolve eq16 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq571 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq541
    | (have j0 := eq541 X0 X1
       grind)
    | exact resolve eq541 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq541
  have eq572 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq571 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq571
    | exact resolve eq571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq633 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq572 (τ X1) X0
       grind)
    | exact superpose eq572 eq18
    | (have j1 := eq572 (τ X1) X0
       grind)
    | exact resolve eq18 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq572
  have eq796 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq633 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq633
    | exact resolve eq633 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq845 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq796
    | (have j0 := eq796 X0 X1
       grind)
    | exact resolve eq796 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq555
       have i₂ := eq845 y x
       grind)
    | exact superpose eq845 eq555
    | (have j1 := eq845 (σ y) (σ x)
       grind)
    | (have r₁ := eq555
       have r₂ := eq845 y x
       grind)
    | exact resolve eq555 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq960
  have eq970 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq961
  have eq976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq555
       have i₂ := eq970
       grind)
    | exact superpose eq970 eq555
    | exact resolve eq555 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq970
  have eq977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq976
  have eq978 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq977
  have eq1032 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq978
  have eq1039 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1032
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1032
    | exact resolve eq1032 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1045 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq16
    | exact resolve eq16 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1094 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1045
       have i₂ := eq845 y x
       grind)
    | exact superpose eq845 eq1045
    | (have j1 := eq845 y x
       grind)
    | (have r₁ := eq1045
       have r₂ := eq845 y x
       grind)
    | exact resolve eq1045 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq1095 : y = (M.op x x) := by grind
  clear eq1094
  have eq1102 : (M.op x y) = (k y x) := by grind
  clear eq1095
  have eq1136 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1045
       have i₂ := eq1102
       grind)
    | exact superpose eq1102 eq1045
    | exact resolve eq1045 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1102
  have eq1139 : False := by grind
  exact eq1139

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq349 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq526 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq349 X0 (σ X1)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 X0 (σ X1)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq577 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq526 X0 (τ X1)
       grind)
    | exact superpose eq526 eq17
    | (have j1 := eq526 X0 (τ X1)
       grind)
    | exact resolve eq17 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq526
  have eq728 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq577 X0 X1
       grind)
    | exact superpose eq577 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq577 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq577 X0 X1
       grind)
    | exact resolve eq13 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq738 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1239 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq537 x y
       grind)
    | exact superpose eq537 eq16
    | (have j1 := eq537 x y
       grind)
    | exact resolve eq16 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1314 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1263
    | (have j0 := eq1263 (τ X1) (τ X0)
       grind)
    | exact resolve eq1263 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1322 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1314
    | (have j0 := eq1314 X0 X1
       grind)
    | exact resolve eq1314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1325 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1322 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1322
    | (have j0 := eq1322 X0 X1
       grind)
    | exact resolve eq1322 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1326 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1325 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1325
    | (have j0 := eq1325 X0 X1
       grind)
    | exact resolve eq1325 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1327 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1326 X0 X0
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
  have eq15820 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq738 X1 X0
       grind)
    | exact superpose eq738 eq10
    | (have j1 := eq738 X1 X0
       grind)
    | exact resolve eq10 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq15877 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15820 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq15820
    | (have j0 := eq15820 X0 X1
       grind)
    | exact resolve eq15820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15820
  have eq15915 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15877 X0 X1
       have j1 := eq12 (τ X0) X1
       grind)
    | (have r₁ := eq15877 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq15877 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15877
  have eq15985 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15915 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq15915
    | exact resolve eq15915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15915
  have eq16295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq1239
       have i₂ := eq15985 y x
       grind)
    | exact superpose eq15985 eq1239
    | (have j1 := eq15985 y x
       grind)
    | exact resolve eq1239 eq15985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq16296 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq15985 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15985
  have eq16297 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq16295
  have eq16525 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16296 (σ y) (σ x)
       have i₂ := eq16297
       grind)
    | exact superpose eq16297 eq16296
    | (have j0 := eq16296 (σ y) (σ x)
       grind)
    | (have r₁ := eq16296 (σ y) (σ x)
       have r₂ := eq16297
       grind)
    | exact resolve eq16296 eq16297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16297
  have eq16526 : (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by grind
  clear eq16525
  have eq16528 : x = (k y x) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16526
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16526
    | exact resolve eq16526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16526
  have eq16555 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1263 x y
       have i₂ := eq16528
       grind)
    | exact superpose eq16528 eq1263
    | (have j0 := eq1263 x y
       grind)
    | (have r₁ := eq1263 x y
       have r₂ := eq16528
       grind)
    | exact resolve eq1263 eq16528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16528
  have eq16582 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) := by grind
  clear eq16555
  have eq16585 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1263 x y
       grind)
    | (have r₁ := eq16582
       have r₂ := eq1263 x y
       grind)
    | exact resolve eq16582 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq16582
  have eq16589 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16585
       grind)
    | exact superpose eq16585 eq16
    | exact resolve eq16 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16595 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16296 (σ y) (σ x)
       have i₂ := eq16585
       grind)
    | exact superpose eq16585 eq16296
    | (have j0 := eq16296 (σ y) (σ x)
       grind)
    | (have r₁ := eq16296 (σ y) (σ x)
       have r₂ := eq16585
       grind)
    | exact resolve eq16296 eq16585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16296 eq16585
  have eq16596 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq16595
  have eq16598 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16596
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16596
    | exact resolve eq16596 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16596
  have eq16623 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq16598
       grind)
    | exact superpose eq16598 eq10
    | exact resolve eq10 eq16598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16598
  have eq16697 : x = (k y x) := by
    first
    | (have i₁ := eq16623
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq16623
    | exact resolve eq16623 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16623
  have eq16778 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1327 y x
       have i₂ := eq16697
       grind)
    | exact superpose eq16697 eq1327
    | (have j0 := eq1327 y x
       grind)
    | (have r₁ := eq1327 y x
       have r₂ := eq16697
       grind)
    | exact resolve eq1327 eq16697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327 eq16697
  have eq16801 : x = (M.op x y) := by grind
  clear eq16778
  have eq16806 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq16589
       have i₂ := eq16801
       grind)
    | exact superpose eq16801 eq16589
    | exact resolve eq16589 eq16801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16589 eq16801
  have eq16820 : False := by grind
  exact eq16820

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2736 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq543 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq568 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq577 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq3593 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq568
    | exact resolve eq568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq3668 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3593 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3593
    | (have j0 := eq3593 X0 X1
       grind)
    | exact resolve eq3593 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3593
  have eq3725 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq577 x y
       grind)
    | exact superpose eq577 eq16
    | (have j1 := eq577 x y
       grind)
    | exact resolve eq16 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3735 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq577 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq7400 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3725
       have i₂ := eq3668 y x
       grind)
    | exact superpose eq3668 eq3725
    | (have j1 := eq3668 y x
       grind)
    | (have r₁ := eq3725
       have r₂ := eq3668 y x
       grind)
    | (have r₁ := eq3725
       have r₂ := eq3668 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3725
       have r₂ := eq3668 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3725 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668 eq3725
  have eq7401 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7400
  have eq7419 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3735 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3735
    | (have j0 := eq3735 (τ X1) (τ X0)
       grind)
    | exact resolve eq3735 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq7477 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7419 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7419
    | (have j0 := eq7419 X0 X1
       grind)
    | exact resolve eq7419 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419
  have eq7512 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7477 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7477
    | (have j0 := eq7477 X0 X1
       grind)
    | exact resolve eq7477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7477
  have eq7544 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7512 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7512
    | (have j0 := eq7512 X0 X1
       grind)
    | exact resolve eq7512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7512
  have eq7570 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7544 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7544
    | (have j0 := eq7544 X0 X1
       grind)
    | exact resolve eq7544 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7544
  have eq7590 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7570 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq7570
    | (have j0 := eq7570 X0 X1
       grind)
    | exact resolve eq7570 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7570
  have eq7609 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7590 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7590
    | (have j0 := eq7590 X0 X1
       grind)
    | exact resolve eq7590 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7590
  have eq7622 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7609 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7609
    | (have j0 := eq7609 X0 X1
       grind)
    | exact resolve eq7609 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7609
  have eq15617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7401
       grind)
    | exact superpose eq7401 eq16
    | exact resolve eq16 eq7401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7401
  have eq15618 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15617
       have r₂ := eq22 x
       grind)
    | exact resolve eq15617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq16048 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15618
       grind)
    | exact superpose eq15618 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15618
       grind)
    | exact resolve eq13 eq15618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15618
  have eq16050 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq16048
  have eq17916 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16050
       grind)
    | exact superpose eq16050 eq16
    | exact resolve eq16 eq16050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16050
  have eq17917 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have r₁ := eq17916
       have r₂ := eq22 x
       grind)
    | exact resolve eq17916 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17916
  have eq17921 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq543 x (σ y)
       have i₂ := eq17917
       grind)
    | exact superpose eq17917 eq543
    | (have j0 := eq543 x (σ y)
       grind)
    | (have r₁ := eq543 x (σ y)
       have r₂ := eq17917
       grind)
    | exact resolve eq543 eq17917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17917
  have eq17935 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq17921
  have eq17936 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq17935
  have eq17943 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq17936
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17936
    | exact resolve eq17936 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17936
  have eq17956 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3735 x y
       have i₂ := eq17943
       grind)
    | exact superpose eq17943 eq3735
    | (have j0 := eq3735 x y
       grind)
    | (have r₁ := eq3735 x y
       have r₂ := eq17943
       grind)
    | exact resolve eq3735 eq17943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17943
  have eq17983 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq17956
  have eq17984 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq17983
  have eq17989 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3735 x y
       grind)
    | (have r₁ := eq17984
       have r₂ := eq3735 x y
       grind)
    | exact resolve eq17984 eq3735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3735 eq17984
  have eq17992 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17989
       grind)
    | exact superpose eq17989 eq16
    | exact resolve eq16 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17994 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq543 x (σ y)
       have i₂ := eq17989
       grind)
    | exact superpose eq17989 eq543
    | (have j0 := eq543 x (σ y)
       grind)
    | (have r₁ := eq543 x (σ y)
       have r₂ := eq17989
       grind)
    | exact resolve eq543 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543 eq17989
  have eq18008 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq17994
  have eq18009 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq18008
  have eq18016 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18009
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18009
    | exact resolve eq18009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18009
  have eq18026 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18016
       grind)
    | exact superpose eq18016 eq10
    | exact resolve eq10 eq18016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18016
  have eq18195 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq18026
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18026
    | exact resolve eq18026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18026
  have eq18197 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18195
       grind)
    | exact superpose eq18195 eq16
    | exact resolve eq16 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195
  have eq18198 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq18197
       have r₂ := eq22 x
       grind)
    | exact resolve eq18197 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18197
  have eq18212 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq18198
       grind)
    | exact superpose eq18198 eq10
    | exact resolve eq10 eq18198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18198
  have eq18382 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq18212
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq18212
    | exact resolve eq18212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18212
  have eq18412 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq7622 y x
       have i₂ := eq18382
       grind)
    | exact superpose eq18382 eq7622
    | (have j0 := eq7622 y x
       grind)
    | (have r₁ := eq7622 y x
       have r₂ := eq18382
       grind)
    | exact resolve eq7622 eq18382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7622 eq18382
  have eq18415 : (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq18412
  have eq18419 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq17992
       have i₂ := eq18415
       grind)
    | exact superpose eq18415 eq17992
    | exact resolve eq17992 eq18415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17992 eq18415
  have eq18428 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq18419
  have eq18429 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18428
       grind)
    | exact superpose eq18428 eq16
    | exact resolve eq16 eq18428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18428
  have eq18432 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq18429
       have r₂ := eq22 x
       grind)
    | exact resolve eq18429 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18429
  have eq18433 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18432
       grind)
    | exact superpose eq18432 eq16
    | exact resolve eq16 eq18432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18434 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18432
       grind)
    | exact superpose eq18432 eq10
    | exact resolve eq10 eq18432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18432
  have eq18603 : x = y := by
    first
    | (have i₁ := eq18434
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18434
    | exact resolve eq18434 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18434
  have eq18604 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18433
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq18433
    | exact resolve eq18433 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18433
  have eq18605 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq18604
       have i₂ := eq18603
       grind)
    | exact superpose eq18603 eq18604
    | exact resolve eq18604 eq18603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18603 eq18604
  have eq18606 : False := by grind
  exact eq18606

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyx_y_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq60 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq77 : (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq74
  have eq78 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq54 eq77
    | exact resolve eq77 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq77
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq82 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq79
  have eq83 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq82
    | exact resolve eq82 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq82
  have eq84 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
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
  have eq85 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq114 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq127 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq78 eq45
    | exact resolve eq45 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78
  have eq128 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq127
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq127
    | exact resolve eq127 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq128 eq11
    | (have j0 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq130
  have eq832 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq928 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq131 eq12
    | (have j0 := eq12 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ x) (σ (M.op x y))
       have r₂ := eq131
       grind)
    | exact resolve eq12 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq131
  have eq938 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq928
  have eq940 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq128 eq938
    | exact resolve eq938 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq938
  have eq941 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq940
  have eq943 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq941
       have r₂ := eq937
       grind)
    | exact resolve eq941 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq941
  have eq1139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1139
    | exact resolve eq1139 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1143 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1140
       have r₂ := eq27
       grind)
    | exact resolve eq1140 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1145 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1143
    | exact resolve eq1143 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1147 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1145
    | exact resolve eq1145 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1204 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1147 eq83
    | exact resolve eq83 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1276 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1204 eq114
    | exact resolve eq114 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204
  have eq1284 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq1276
    | exact resolve eq1276 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1478 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1284
       grind)
    | exact superpose eq1284 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284
  have eq1479 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1478
  have eq1481 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1479
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1479
    | exact resolve eq1479 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1482 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1481
  have eq1486 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1482
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1482
    | exact resolve eq1482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1487 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1486
  have eq1491 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1487 eq27
    | exact resolve eq27 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1497 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1487 eq83
    | exact resolve eq83 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1498 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1487 eq85
    | (have r₁ := eq85
       have r₂ := eq1487
       grind)
    | exact resolve eq85 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1487
  have eq1503 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1498
  have eq2648 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1503 eq114
    | exact resolve eq114 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1503
  have eq2657 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2648
    | exact resolve eq2648 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2648
  have eq2660 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2657
       have r₂ := eq84
       grind)
    | exact resolve eq2657 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2657
  have eq2666 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq2660
       grind)
    | exact superpose eq2660 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2660
  have eq2667 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2666
  have eq2671 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2667
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2667
    | exact resolve eq2667 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq2672 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2671
  have eq2676 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2672
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2672
    | exact resolve eq2672 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2672
  have eq2705 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2676 eq29
    | exact resolve eq29 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2709 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2676 eq118
    | exact resolve eq118 eq2676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq2676
  have eq2727 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq2709
  have eq2735 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2705
    | exact resolve eq2705 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2705
  have eq2738 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2735 eq20
    | exact resolve eq20 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2774 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2738
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2738
    | exact resolve eq2738 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2806 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2774 eq26
    | exact resolve eq26 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq943 eq2806
    | exact resolve eq2806 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq2846 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq2843
       have r₂ := eq27
       grind)
    | exact resolve eq2843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq2848 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2846 eq20
    | exact resolve eq20 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2855 : x ≠ x ∨ x = y ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq2846 eq84
    | (have r₁ := eq84
       have r₂ := eq2846
       grind)
    | exact resolve eq84 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq2872 : x ≠ x ∨ x = y ∨ y = (k x y) := by grind
  clear eq2855
  have eq2873 : y = (k x y) ∨ x = y := by grind
  clear eq2872
  have eq2885 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2848
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2848
    | exact resolve eq2848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq2998 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq2873
       grind)
    | exact superpose eq2873 eq44
    | exact resolve eq44 eq2873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq3005 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2998
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2998
    | exact resolve eq2998 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998
  have eq3280 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2885 eq3005
    | exact resolve eq3005 eq2885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885
  have eq3289 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3005 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq3005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3290 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq3289
  have eq3293 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq3280
  have eq3294 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq3290
    | exact resolve eq3290 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq3294
    | exact resolve eq3294 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3294
  have eq6422 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq832 x y
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq832
    | (have j0 := eq832 x y
       grind)
    | exact resolve eq832 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq832
  have eq6472 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6422
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6422
    | exact resolve eq6422 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6422
  have eq6531 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6472
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6472
    | exact resolve eq6472 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6472
  have eq6584 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6531
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6531
    | exact resolve eq6531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6531
  have eq6634 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6584
    | exact resolve eq6584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6584
  have eq6670 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6634
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6634
    | exact resolve eq6634 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6634
  have eq6693 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6670
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6670
    | exact resolve eq6670 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6670
  have eq6705 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6693
    | exact resolve eq6693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6693
  have eq11150 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2727 eq1497
    | exact resolve eq1497 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq2727
  have eq11173 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq11150
  have eq11177 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11173
       have r₂ := eq1491
       grind)
    | exact resolve eq11173 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491 eq11173
  have eq11763 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq11177
  have eq11766 : x = (M.op x y) := by
    first
    | (have r₁ := eq11763
       have r₂ := eq2846
       grind)
    | exact resolve eq11763 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846 eq11763
  have eq11781 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq11766 eq20
    | exact resolve eq20 eq11766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq11766
  have eq11853 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11781
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11781
    | exact resolve eq11781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11781
  have eq11854 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq11853 eq26
    | exact resolve eq26 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq11863 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq11853 eq83
    | exact resolve eq83 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq11881 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq11853 eq943
    | exact resolve eq943 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq12265 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3297 eq11863
    | exact resolve eq11863 eq3297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3297 eq11863
  have eq12287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq11853 eq12265
    | exact resolve eq12265 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12265
  have eq12288 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq12287
       have r₂ := eq27
       grind)
    | exact resolve eq12287 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12287
  have eq12852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | exact superpose eq11853 eq6705
    | exact resolve eq6705 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6705
  have eq12853 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq12852
       have r₂ := eq27
       grind)
    | exact resolve eq12852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12852
  have eq12854 : (σ y) ≠ (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11853 eq12853
    | exact resolve eq12853 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12853
  have eq12935 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3293 eq12854
    | (have r₁ := eq12854
       have r₂ := eq3293
       grind)
    | exact resolve eq12854 eq3293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12854
  have eq12937 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq12935
  have eq12940 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq12937 eq27
    | exact resolve eq27 eq12937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937
  have eq13123 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12288 eq3293
    | exact resolve eq3293 eq12288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3293 eq12288
  have eq13137 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq13123
  have eq13144 : x = y := by
    first
    | (have r₁ := eq13137
       have r₂ := eq12940
       grind)
    | exact resolve eq13137 eq12940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12940 eq13137
  have eq13154 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq13144
       grind)
    | exact superpose eq13144 eq24
    | exact resolve eq24 eq13144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq13144
  have eq13182 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13154
    | exact resolve eq13154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13154
  have eq13196 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11853 eq13182
    | exact resolve eq13182 eq11853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11853 eq13182
  have eq13244 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13196 eq11854
    | exact resolve eq11854 eq13196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11854 eq13196
  have eq13255 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11881 eq13244
    | exact resolve eq13244 eq11881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11881 eq13244
  have eq13269 : False := by grind
  exact eq13269

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_pyy_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 X1) X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : x ≠ x ∨ (M.op x (M.op x y)) = (k (M.op x y) x) := by
    first
    | exact superpose eq54 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq54
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq55 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq69
  have eq71 : (M.op x (M.op x y)) = (k (M.op x y) x) := by grind
  clear eq67
  have eq74 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq60 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq60
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq74
  have eq78 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq54 eq77
    | exact resolve eq77 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq62 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq62
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq79
  have eq83 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq82
    | exact resolve eq82 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq94 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq62 eq70
    | exact resolve eq70 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq70
  have eq111 : (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq60 eq71
    | exact resolve eq71 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq71
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  clear eq44
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq122 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq125 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq126 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq127 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
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
  have eq130 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq78 eq45
    | exact resolve eq45 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq78
  have eq131 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq130
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq130
    | exact resolve eq130 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq132 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq11 sF2 sF1
       grind)
    | exact superpose eq11 eq131
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq139 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq125
       grind)
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq111 eq145
    | exact resolve eq145 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq145
  have eq151 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq150
    | exact resolve eq150 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq152 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq151
       have i₂ := eq11 sF1 sF2
       grind)
    | exact superpose eq11 eq151
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (σ (k y (k y y))) = (k (σ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq36 (k y y)
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq36
    | exact resolve eq36 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq163 : (σ (k (M.op x y) (k y (M.op x y)))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq127 eq37
    | exact resolve eq37 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq127
  have eq298 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq302 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq304 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq302 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq302
    | exact resolve eq302 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq319 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq355 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq16
    | exact resolve eq16 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq743 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 (M.op (σ X0) X1)
       have i₂ := eq304 (σ X0) X1
       grind)
    | exact superpose eq304 eq407
    | exact resolve eq407 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq771 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq743 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq743
    | exact resolve eq743 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq824 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq53
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq53 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq5606 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq128 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq128
    | (have j0 := eq128 y
       grind)
    | exact resolve eq128 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq5626 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq5606
  have eq5632 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5626
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq5626
    | exact resolve eq5626 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5626
  have eq5655 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq5632
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq5632 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5632
  have eq5833 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq148
    | (have j0 := eq148 (M.op x y)
       grind)
    | exact resolve eq148 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq5852 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5833
  have eq5857 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq147 eq5852
    | exact resolve eq5852 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852
  have eq5887 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5857
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5857 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857
  have eq7772 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq121 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq7772
    | exact resolve eq7772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7772
  have eq7784 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq7773
       have r₂ := eq27
       grind)
    | exact resolve eq7773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7773
  have eq7788 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq7784
    | exact resolve eq7784 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7784
  have eq7794 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq7788 eq53
    | exact resolve eq53 eq7788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7788
  have eq7809 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq7794
    | exact resolve eq7794 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7794
  have eq7810 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7809
  have eq7818 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq7810
       grind)
    | exact superpose eq7810 eq53
    | exact resolve eq53 eq7810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7810
  have eq7833 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7818
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7818
    | exact resolve eq7818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7818
  have eq7834 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq7833
  have eq7844 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7834 eq83
    | exact resolve eq83 eq7834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq7845 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7834 eq94
    | exact resolve eq94 eq7834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq7834
  have eq8500 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7844 eq121
    | exact resolve eq121 eq7844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq7844
  have eq8509 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq8500
  have eq8523 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7845 eq139
    | exact resolve eq139 eq7845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq7845
  have eq8538 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq8523
    | exact resolve eq8523 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8523
  have eq8803 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq8538
       grind)
    | exact superpose eq8538 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8538
  have eq8804 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8803
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8803
    | exact resolve eq8803 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8803
  have eq8805 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq8804
  have eq10598 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq824 y x
       have i₂ := eq125
       grind)
    | exact superpose eq125 eq824
    | (have j0 := eq824 y x
       grind)
    | exact resolve eq824 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq824
  have eq10756 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10598
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10598
    | exact resolve eq10598 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10598
  have eq10877 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10756
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10756
    | exact resolve eq10756 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10756
  have eq10991 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10877
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10877
    | exact resolve eq10877 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10877
  have eq11083 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq10991
    | exact resolve eq10991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10991
  have eq11171 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq11083
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11083
    | exact resolve eq11083 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11083
  have eq11246 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11171
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11171
    | exact resolve eq11171 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11171
  have eq11366 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq8509
       grind)
    | exact superpose eq8509 eq53
    | exact resolve eq53 eq8509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8509
  have eq11381 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11366
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11366
    | exact resolve eq11366 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11366
  have eq11382 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq11381
  have eq11387 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11382 eq28
    | exact resolve eq28 eq11382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11382
  have eq11522 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq11387
    | exact resolve eq11387 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq11536 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11522 eq20
    | exact resolve eq20 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11546 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11522 eq141
    | exact resolve eq141 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq11551 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11522 eq147
    | exact resolve eq147 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq11553 : (σ (k y (k y y))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11522 eq163
    | exact resolve eq163 eq11522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq11522
  have eq11621 : (k (σ y) (k (σ y) (σ y))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11553
       have i₂ := eq156
       grind)
    | exact superpose eq156 eq11553
    | exact resolve eq11553 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq11553
  have eq11623 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5887 eq11551
    | exact resolve eq11551 eq5887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11551
  have eq11628 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11546 X0
       have i₂ := eq122 X0
       grind)
    | exact superpose eq122 eq11546
    | exact resolve eq11546 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq11546
  have eq11631 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11536
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11536
    | exact resolve eq11536 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11536
  have eq11651 : (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) = (k (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5655 eq11621
    | exact resolve eq11621 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11621
  have eq11653 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11623
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq11623
    | exact resolve eq11623 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq11623
  have eq11672 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11651
       have i₂ := eq304 sF3 sF3
       grind)
    | exact superpose eq304 eq11651
    | exact resolve eq11651 eq304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304 eq11651
  have eq11674 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5655 eq11653
    | exact resolve eq11653 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq11653
  have eq11770 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11631 eq26
    | exact resolve eq26 eq11631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20067 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11628 eq319
    | exact resolve eq319 eq11628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11628
  have eq20165 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20067 x
       have i₂ := eq319 sF1 x
       grind)
    | exact superpose eq319 eq20067
    | exact resolve eq20067 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq20067
  have eq20193 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq20165
    | exact resolve eq20165 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20165
  have eq20204 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq20193
    | exact resolve eq20193 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20193
  have eq21509 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11674 eq53
    | exact resolve eq53 eq11674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11674
  have eq26192 : ∀ X0 : G, (M.op x y) = (k y (τ (M.op (σ (M.op x y)) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20204 eq771
    | exact resolve eq771 eq20204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq20204
  have eq26294 : ∀ X0 : G, (M.op x y) = (τ (k (σ y) (M.op (σ (M.op x y)) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26192 X0
       have i₂ := eq355 (M.op (σ sF0) X0)
       grind)
    | exact superpose eq355 eq26192
    | exact resolve eq26192 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355 eq26192
  have eq26343 : ∀ X0 : G, (M.op x y) = (τ (k (σ y) (M.op (σ (M.op x y)) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq26294
    | (have j0 := eq26294 X0
       grind)
    | exact resolve eq26294 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26294
  have eq38913 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11770 eq132
    | exact resolve eq132 eq11770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq38949 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq38913
       have r₂ := eq27
       grind)
    | exact resolve eq38913 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38913
  have eq44452 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26343 eq15
    | exact resolve eq15 eq26343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26343
  have eq44519 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq44452
    | (have j0 := eq44452 X0
       grind)
    | exact resolve eq44452 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44452
  have eq44668 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38949 eq53
    | exact resolve eq53 eq38949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38949
  have eq45320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44668 eq11770
    | exact resolve eq11770 eq44668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44668
  have eq45351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45320
  have eq45354 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45351
       have r₂ := eq27
       grind)
    | exact resolve eq45351 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45351
  have eq45410 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45354 eq55
    | exact resolve eq55 eq45354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq45539 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq45410 eq14
    | exact resolve eq14 eq45410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45410
  have eq45673 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11631 eq11246
    | exact resolve eq11246 eq11631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11246
  have eq45705 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq45673
       have r₂ := eq27
       grind)
    | exact resolve eq45673 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45673
  have eq45707 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq151 eq45705
    | exact resolve eq45705 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq45705
  have eq818313 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21509 eq45539
    | exact resolve eq45539 eq21509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21509 eq45539
  have eq818754 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq818313
  have eq818782 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq818754
    | exact resolve eq818754 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818754
  have eq924287 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45354 eq818782
    | exact resolve eq818782 eq45354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45354 eq818782
  have eq924422 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq924287
  have eq1110923 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq8805
       grind)
    | exact superpose eq8805 eq53
    | exact resolve eq53 eq8805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8805
  have eq1178546 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq45707 eq53
    | exact resolve eq53 eq45707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45707
  have eq1497501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1178546 eq11770
    | exact resolve eq11770 eq1178546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11770 eq1178546
  have eq1497696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1497501
  have eq1497700 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1497696
       have r₂ := eq27
       grind)
    | exact resolve eq1497696 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497696
  have eq1499890 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1497700 eq44519
    | exact resolve eq44519 eq1497700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44519 eq1497700
  have eq1501015 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1499890
  have eq1501102 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1501015 eq11672
    | exact resolve eq11672 eq1501015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11672 eq1501015
  have eq1501266 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1501102
  have eq1501289 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5887 eq1501266
    | exact resolve eq1501266 eq5887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887 eq1501266
  have eq1514355 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1501289 eq924422
    | exact resolve eq924422 eq1501289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924422 eq1501289
  have eq1515552 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1514355
  have eq1515585 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1515552
    | exact resolve eq1515552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515552
  have eq1515602 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1515585 eq27
    | exact resolve eq27 eq1515585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515585
  have eq1516344 : x = (M.op x y) := by
    first
    | (have r₁ := eq1515602
       have r₂ := eq11631
       grind)
    | exact resolve eq1515602 eq11631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11631 eq1515602
  have eq1516346 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1516344 eq20
    | exact resolve eq20 eq1516344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1516348 : x = (M.op x x) := by
    first
    | exact superpose eq1516344 eq54
    | exact resolve eq54 eq1516344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1517573 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1516346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1516346
    | exact resolve eq1516346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516346
  have eq1517618 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1517573 eq26
    | exact resolve eq26 eq1517573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1517640 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1517573 eq152
    | exact resolve eq152 eq1517573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq1519239 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1517640
  have eq1519509 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x X1
       have i₂ := eq1516348
       grind)
    | exact superpose eq1516348 eq14
    | exact resolve eq14 eq1516348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516348
  have eq1676206 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1519509 y y
       have i₂ := eq1110923
       grind)
    | exact superpose eq1110923 eq1519509
    | exact resolve eq1519509 eq1110923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110923 eq1519509
  have eq1676560 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1676206
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1676206
    | exact resolve eq1676206 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676206
  have eq1677227 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1516344 eq1676560
    | exact resolve eq1676560 eq1516344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676560
  have eq1677686 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1677227
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1677227
    | exact resolve eq1677227 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677227
  have eq1677687 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq1677686
  have eq1677907 : x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq1516344 eq1677687
    | exact resolve eq1677687 eq1516344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677687
  have eq1682745 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq1677907
       grind)
    | exact superpose eq1677907 eq53
    | exact resolve eq53 eq1677907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1677907
  have eq1682916 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1682745
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1682745
    | exact resolve eq1682745 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1682745
  have eq1682938 : x = y ∨ x = y := by
    first
    | exact superpose eq1516344 eq1682916
    | exact resolve eq1682916 eq1516344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516344 eq1682916
  have eq1682939 : x = y := by grind
  clear eq1682938
  have eq1682956 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1682939
       grind)
    | exact superpose eq1682939 eq24
    | exact resolve eq24 eq1682939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1682939
  have eq1683776 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1682956
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1682956
    | exact resolve eq1682956 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1682956
  have eq1683930 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1517573 eq1683776
    | exact resolve eq1683776 eq1517573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517573 eq1683776
  have eq1691789 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1683930 eq1517618
    | exact resolve eq1517618 eq1683930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517618 eq1683930
  have eq1691809 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1519239 eq1691789
    | exact resolve eq1691789 eq1519239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519239 eq1691789
  have eq1692505 : False := by grind
  exact eq1692505

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_x_pxx_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (k (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq10
    | exact resolve eq10 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq60 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq60
    | (have j0 := eq60 x y
       grind)
    | exact resolve eq60 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq60
    | (have j0 := eq60 (σ x) (σ y)
       grind)
    | exact resolve eq60 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq63 eq60
    | exact resolve eq60 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : x ≠ x ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq63 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq63
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq73
  have eq76 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq64 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq64
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq77
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq91 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq71 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq71
       grind)
    | exact resolve eq13 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq92 : x = (k x (M.op x y)) := by grind
  clear eq91
  have eq108 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq113 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq92 eq46
    | exact resolve eq46 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq92
  have eq114 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq113
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq113
    | exact resolve eq113 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : (σ (k y (k y x))) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq37 (k y x)
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq37
    | exact resolve eq37 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : (σ (k (M.op x y) (k x y))) = (k (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq38 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq38
    | exact resolve eq38 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq74 eq127
    | exact resolve eq127 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq127
  have eq133 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq132
    | exact resolve eq132 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq142 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq290 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11 (τ X0) X1
       grind)
    | exact superpose eq11 eq35
    | (have j1 := eq11 (τ X0) X1
       grind)
    | exact resolve eq35 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq370 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (σ (k y (k X0 (τ X1)))) = (k (σ y) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq37
    | exact resolve eq37 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq417 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq76 eq70
    | exact resolve eq70 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq527 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq529 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq2340 : ∀ X0 X1 : G, (k (σ y) (k (σ X0) X1)) = (σ (k y (M.op X0 (τ X1)))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq11 X0 (τ X1)
       grind)
    | exact superpose eq11 eq372
    | (have j1 := eq11 X0 (τ X1)
       grind)
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq3859 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq529 y
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq529
    | (have j0 := eq529 y
       grind)
    | exact resolve eq529 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq3864 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3859
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3859
    | exact resolve eq3859 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3859
  have eq3870 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3864
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3864
    | exact resolve eq3864 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3864
  have eq5661 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq290 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq290
    | exact resolve eq290 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq5753 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5661 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq5661
    | (have j0 := eq5661 X0 X1
       grind)
    | exact resolve eq5661 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661
  have eq6722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6723 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6722
    | exact resolve eq6722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6722
  have eq6734 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq6723
       have r₂ := eq28
       grind)
    | exact resolve eq6723 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6723
  have eq6738 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6734
    | exact resolve eq6734 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6734
  have eq6852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq6738 eq60
    | exact resolve eq60 eq6738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6738
  have eq6905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq6852
    | exact resolve eq6852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6852
  have eq6906 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6905
  have eq6915 : x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq6906
       grind)
    | exact superpose eq6906 eq70
    | exact resolve eq70 eq6906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6906
  have eq6962 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq6915
       have r₂ := eq51
       grind)
    | exact resolve eq6915 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6915
  have eq6984 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq6962
       grind)
    | exact superpose eq6962 eq45
    | exact resolve eq45 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6962
  have eq6999 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6984
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6984
    | exact resolve eq6984 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984
  have eq7004 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq6999
       have r₂ := eq52
       grind)
    | exact resolve eq6999 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq6999
  have eq7006 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq88 eq7004
    | exact resolve eq7004 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq7010 : (τ (σ x)) = (k x y) := by
    first
    | exact superpose eq7004 eq56
    | exact resolve eq56 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7018 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7004 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7019 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7018
    | exact resolve eq7018 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7018
  have eq7026 : x = (k x y) := by
    first
    | exact superpose eq29 eq7010
    | exact resolve eq7010 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7010
  have eq7030 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq7019
    | exact resolve eq7019 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq7077 : (σ (k (M.op x y) (k x y))) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq130 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq130
    | exact resolve eq130 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq130
  have eq7136 : (σ (k (M.op x y) (k x y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq7004 eq7077
    | exact resolve eq7077 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7077
  have eq7151 : (k (σ (M.op x y)) (k (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq125 eq7136
    | exact resolve eq7136 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq7136
  have eq7160 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq7004 eq7151
    | exact resolve eq7151 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7151
  have eq7166 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq133 eq7160
    | exact resolve eq7160 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq7160
  have eq7170 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ (M.op x y)) (k (σ x) (σ y))) := by
    first
    | exact superpose eq7004 eq7166
    | exact resolve eq7166 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7166
  have eq7175 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq7004 eq7170
    | exact resolve eq7170 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq8187 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq60 y y
       have i₂ := eq7006
       grind)
    | exact superpose eq7006 eq60
    | exact resolve eq60 eq7006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7006
  have eq8200 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8187
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8187
    | exact resolve eq8187 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8187
  have eq8201 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq8200
  have eq8204 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8201 eq29
    | exact resolve eq29 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq8221 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8201 eq114
    | exact resolve eq114 eq8201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq8201
  have eq8304 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq8204
    | exact resolve eq8204 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8204
  have eq8315 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8304 eq21
    | exact resolve eq21 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8328 : (σ (k y y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8304 eq129
    | exact resolve eq129 eq8304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq8304
  have eq8399 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8328
       have i₂ := eq109
       grind)
    | exact superpose eq109 eq8328
    | exact resolve eq8328 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq8328
  have eq8406 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8315
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8315
    | exact resolve eq8315 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315
  have eq9163 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8406 eq27
    | exact resolve eq27 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9446 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8221 eq175
    | exact resolve eq175 eq8221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq8221
  have eq9483 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq9446
    | exact resolve eq9446 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9446
  have eq13932 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9483 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq9483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq13944 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq13932
  have eq14339 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq7175 eq60
    | exact resolve eq60 eq7175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7175
  have eq14915 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq13944 eq14
    | exact resolve eq14 eq13944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13944
  have eq18328 : (σ y) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8399 eq3870
    | exact resolve eq3870 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870 eq8399
  have eq28099 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7030 eq60
    | exact resolve eq60 eq7030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7030
  have eq28118 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28099
    | exact resolve eq28099 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28099
  have eq28119 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28118
  have eq28122 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28119 eq28
    | exact resolve eq28 eq28119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28128 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28119 eq78
    | exact resolve eq78 eq28119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq28119
  have eq28207 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8406 eq28122
    | (have r₁ := eq28122
       have r₂ := eq8406
       grind)
    | exact resolve eq28122 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28122
  have eq28208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq28207
  have eq28215 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28208 eq64
    | exact resolve eq64 eq28208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq28491 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 X1)) X0) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq28215 eq14
    | exact resolve eq14 eq28215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28215
  have eq134425 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7004 eq5753
    | (have j0 := eq5753 (σ x) (σ y)
       grind)
    | exact resolve eq5753 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5753 eq7004
  have eq135104 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq134425
    | exact resolve eq134425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134425
  have eq135363 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq135104
    | exact resolve eq135104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135104
  have eq347354 : ∀ X0 : G, (k (σ y) (k (σ X0) (k (σ x) (σ y)))) = (σ (k y (M.op X0 (k x y)))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | exact superpose eq56 eq2340
    | exact resolve eq2340 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2340
  have eq347583 : ∀ X0 : G, (k (σ y) (k (σ X0) (k (σ x) (σ y)))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq347354 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347354
    | (have j0 := eq347354 X0
       grind)
    | exact resolve eq347354 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347354
  have eq347623 : ∀ X0 : G, (k (σ y) (σ (k X0 (k x y)))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | exact superpose eq54 eq347583
    | (have j0 := eq347583 X0
       grind)
    | exact resolve eq347583 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq347583
  have eq347651 : ∀ X0 : G, (σ (k y (k X0 (k x y)))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | exact superpose eq37 eq347623
    | (have j0 := eq347623 X0
       grind)
    | exact resolve eq347623 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq347623
  have eq347658 : ∀ X0 : G, (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) ∨ (M.op (k x y) (k x y)) = X0 ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq347651 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347651
    | (have j0 := eq347651 X0
       grind)
    | exact resolve eq347651 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347651
  have eq347665 : ∀ X0 : G, (M.op x x) = X0 ∨ (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) ∨ (k x y) = (M.op X0 (k x y)) := by
    intro X0
    first
    | (have i₁ := eq347658 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347658
    | (have j0 := eq347658 X0
       grind)
    | exact resolve eq347658 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347658
  have eq347672 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op x x) = X0 ∨ (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq347665 X0
       have i₂ := eq7026
       grind)
    | exact superpose eq7026 eq347665
    | (have j0 := eq347665 X0
       grind)
    | exact resolve eq347665 eq7026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026 eq347665
  have eq412783 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq135363 eq60
    | exact resolve eq60 eq135363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135363
  have eq412873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq412783
    | exact resolve eq412783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412783
  have eq412874 : (σ (σ x)) = (σ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq412873
  have eq412926 : ∀ X0 : G, (τ (k (σ (σ x)) X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq412874 eq370
    | exact resolve eq370 eq412874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412874
  have eq413114 : ∀ X0 : G, (k (σ x) (τ X0)) = (k (M.op (σ x) (σ y)) (τ X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq412926 x
       have i₂ := eq370 sF2 x
       grind)
    | exact superpose eq370 eq412926
    | exact resolve eq412926 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq412926
  have eq413895 : ∀ X0 : G, (k (σ x) X0) = (k (M.op (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq413114 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq413114
    | exact resolve eq413114 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413114
  have eq414404 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op X0 X0) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq417 eq413895
    | exact resolve eq413895 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq413895
  have eq2247212 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq14339 eq66
    | exact resolve eq66 eq14339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq14339
  have eq2247413 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq2247212
  have eq2247425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2247413 eq9163
    | exact resolve eq9163 eq2247413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9163
  have eq2247691 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2247425
       have r₂ := eq28
       grind)
    | exact resolve eq2247425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247425
  have eq2247790 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2247691 eq70
    | exact resolve eq70 eq2247691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2247691
  have eq2250082 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2247790 eq18328
    | exact resolve eq18328 eq2247790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18328 eq2247790
  have eq2250479 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2250082
  have eq2250487 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2250479
       have r₂ := eq8406
       grind)
    | exact resolve eq2250479 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2250479
  have eq2253540 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2250487 eq28491
    | exact resolve eq28491 eq2250487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28491 eq2250487
  have eq2253569 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2253540
  have eq2253604 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2253569
    | exact resolve eq2253569 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253569
  have eq2261523 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28208 eq2253604
    | exact resolve eq2253604 eq28208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28208 eq2253604
  have eq2261756 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2261523
  have eq2261770 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq2261756
    | exact resolve eq2261756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2261756
  have eq2261775 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2261770 eq28
    | exact resolve eq28 eq2261770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261770
  have eq2263109 : x = (M.op x y) := by
    first
    | (have r₁ := eq2261775
       have r₂ := eq8406
       grind)
    | exact resolve eq2261775 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406 eq2261775
  have eq2263119 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2263109 eq21
    | exact resolve eq21 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2263122 : x = (M.op x x) := by
    first
    | exact superpose eq2263109 eq63
    | exact resolve eq63 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2264772 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2263119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2263119
    | exact resolve eq2263119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263119
  have eq2265211 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2264772 eq28128
    | exact resolve eq28128 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28128
  have eq2266839 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2264772 eq2247413
    | exact resolve eq2247413 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247413
  have eq2266841 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2266839
  have eq2267027 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2265211
       have r₂ := eq28
       grind)
    | exact resolve eq2265211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265211
  have eq2275346 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2266841 eq414404
    | exact resolve eq414404 eq2266841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414404 eq2266841
  have eq2275572 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2264772 eq2275346
    | exact resolve eq2275346 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275346
  have eq2276139 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2275572
       have i₂ := eq278 sF1 sF1
       grind)
    | exact superpose eq278 eq2275572
    | exact resolve eq2275572 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275572
  have eq2276351 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2276139
       have r₂ := eq28
       grind)
    | exact resolve eq2276139 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2276139
  have eq2276569 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2276351 eq28
    | exact resolve eq28 eq2276351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2276351
  have eq3037320 : ∀ X0 : G, (σ (k y (k X0 x))) = (σ (k y (M.op X0 x))) ∨ x = (M.op X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have i₁ := eq347672 X0
       have i₂ := eq2263122
       grind)
    | exact superpose eq2263122 eq347672
    | (have j0 := eq347672 X0
       grind)
    | exact resolve eq347672 eq2263122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347672 eq2263122
  have eq3038049 : (k (σ y) (k (σ y) (σ x))) = (σ (k y (M.op y x))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq118
       have i₂ := eq3037320 y
       grind)
    | exact superpose eq3037320 eq118
    | (have j1 := eq3037320 y
       grind)
    | exact resolve eq118 eq3037320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq3037320
  have eq3039027 : (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3038049
       have i₂ := eq278 y x
       grind)
    | exact superpose eq278 eq3038049
    | exact resolve eq3038049 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq3038049
  have eq3039271 : (σ y) = (k (σ y) (k (σ y) (σ (M.op x y)))) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2264772 eq3039027
    | exact resolve eq3039027 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039027
  have eq3039457 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2267027 eq3039271
    | exact resolve eq3039271 eq2267027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267027 eq3039271
  have eq3039534 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3039457
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3039457
    | exact resolve eq3039457 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039457
  have eq3072673 : (τ (σ y)) = (k y y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3039534 eq142
    | exact resolve eq142 eq3039534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq3039534
  have eq3073223 : y = (k y y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq30 eq3072673
    | exact resolve eq3072673 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3072673
  have eq3078089 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq3073223
       grind)
    | exact superpose eq3073223 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq3073223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073223
  have eq3078214 : y = (M.op y y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq3078089
  have eq3080709 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq14915 y y
       have i₂ := eq3078214
       grind)
    | exact superpose eq3078214 eq14915
    | exact resolve eq14915 eq3078214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14915 eq3078214
  have eq3080812 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2263109 eq3080709
    | exact resolve eq3080709 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080709
  have eq3081445 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3080812
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3080812
    | exact resolve eq3080812 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3080812
  have eq3081851 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2263109 eq3081445
    | exact resolve eq3081445 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081445
  have eq3082014 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3081851
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3081851
    | exact resolve eq3081851 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3081851
  have eq3082015 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq3082014
  have eq3082082 : x = y ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2263109 eq3082015
    | exact resolve eq3082015 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082015
  have eq3082083 : x = (M.op y x) ∨ x = y := by grind
  clear eq3082082
  have eq3082213 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq60 y x
       have i₂ := eq3082083
       grind)
    | exact superpose eq3082083 eq60
    | exact resolve eq60 eq3082083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq3082083
  have eq3082495 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3082213
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3082213
    | exact resolve eq3082213 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3082213
  have eq3082536 : x = y ∨ x = y := by
    first
    | exact superpose eq2263109 eq3082495
    | exact resolve eq3082495 eq2263109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263109 eq3082495
  have eq3082537 : x = y := by grind
  clear eq3082536
  have eq3082568 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3082537
       grind)
    | exact superpose eq3082537 eq25
    | exact resolve eq25 eq3082537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3082537
  have eq3083458 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3082568
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3082568
    | exact resolve eq3082568 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3082568
  have eq3083617 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2264772 eq3083458
    | exact resolve eq3083458 eq2264772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264772 eq3083458
  have eq3083711 : False := by grind
  exact eq3083711
