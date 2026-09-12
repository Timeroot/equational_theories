import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_y_Equation2725 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law2725 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = b :=
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
  clear eq37
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op X0 (M.op (M.op X1 X1) X0)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
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
  have eq536 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) ∨ X2 = X3 := by
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
  have eq1377 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq536 y x
       grind)
    | exact superpose eq536 eq95
    | (have j1 := eq536 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq95 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1395 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1377
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1377
    | exact resolve eq1377 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1396 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
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

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq24
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq84
    | (have j0 := eq84 X0
       grind)
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq84
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | (have j0 := eq91 X0
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq92 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq92 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq92 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq96 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq93 (σ X0)
       grind)
    | exact superpose eq93 eq15
    | exact resolve eq15 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq96
    | exact resolve eq96 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq96
  have eq260 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq78 x y
       grind)
    | exact superpose eq78 eq16
    | (have j1 := eq78 x y
       grind)
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq748 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq80
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq794 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq748
    | (have j0 := eq748 X0 X1
       grind)
    | exact resolve eq748 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq942 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq267 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq267
    | (have j0 := eq267 (τ X0) (τ X1)
       grind)
    | exact resolve eq267 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq950 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq942 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq942
    | (have j0 := eq942 X0 X1
       grind)
    | exact resolve eq942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq953 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq950 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq950
    | (have j0 := eq950 X0 X1
       grind)
    | exact resolve eq950 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq955 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq953 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq953
    | (have j0 := eq953 X0 X1
       grind)
    | exact resolve eq953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953
  have eq956 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq955 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq955
    | (have j0 := eq955 X0 X1
       grind)
    | exact resolve eq955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq957 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq958 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq957 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq957
    | (have j0 := eq957 X0 X1
       grind)
    | exact resolve eq957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1318 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq260
       have i₂ := eq794 y x
       grind)
    | exact superpose eq794 eq260
    | (have j1 := eq794 (σ x) (σ y)
       grind)
    | (have r₁ := eq260
       have r₂ := eq794 y x
       grind)
    | (have r₁ := eq260
       have r₂ := eq794 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq260
       have r₂ := eq794 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq260 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq794
  have eq1319 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1318
  have eq30271 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1319
       grind)
    | exact superpose eq1319 eq16
    | exact resolve eq16 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq30272 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq30271
       have r₂ := eq107 x
       grind)
    | exact resolve eq30271 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30271
  have eq30591 : x ≠ x ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq30272
       grind)
    | exact superpose eq30272 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq30272
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq30272
       grind)
    | exact resolve eq12 eq30272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30272
  have eq30599 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30591
  have eq30603 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq267 x y
       have i₂ := eq30599
       grind)
    | exact superpose eq30599 eq267
    | (have j0 := eq267 x y
       grind)
    | exact resolve eq267 eq30599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq30599
  have eq30622 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq30603
  have eq30623 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq30622
  have eq30797 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq16
    | exact resolve eq16 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30806 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq30623
       grind)
    | exact superpose eq30623 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq30623
       grind)
    | exact resolve eq12 eq30623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30623
  have eq30814 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq30806
  have eq30823 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq30814
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq30814
    | exact resolve eq30814 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30814
  have eq31098 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30823
       grind)
    | exact superpose eq30823 eq10
    | exact resolve eq10 eq30823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30823
  have eq31213 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq31098
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31098
    | exact resolve eq31098 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31098
  have eq31222 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31213
       grind)
    | exact superpose eq31213 eq16
    | exact resolve eq16 eq31213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31213
  have eq31223 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq31222
       have r₂ := eq107 x
       grind)
    | exact resolve eq31222 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31222
  have eq31502 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq31223
       grind)
    | exact superpose eq31223 eq10
    | exact resolve eq10 eq31223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31223
  have eq31621 : x = (k y x) := by
    first
    | (have i₁ := eq31502
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq31502
    | exact resolve eq31502 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31502
  have eq31638 : x ≠ x ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq958 y x
       have i₂ := eq31621
       grind)
    | exact superpose eq31621 eq958
    | (have j0 := eq958 x y
       grind)
    | (have r₁ := eq958 y x
       have r₂ := eq31621
       grind)
    | exact resolve eq958 eq31621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq31621
  have eq31648 : x = y ∨ x = (M.op x y) := by grind
  clear eq31638
  have eq32102 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq31648
       grind)
    | exact superpose eq31648 eq16
    | exact resolve eq16 eq31648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31648
  have eq32107 : x = (M.op x y) := by
    first
    | (have r₁ := eq32102
       have r₂ := eq107 x
       grind)
    | exact resolve eq32102 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32102
  have eq32111 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30797
       have i₂ := eq32107
       grind)
    | exact superpose eq32107 eq30797
    | exact resolve eq30797 eq32107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30797 eq32107
  have eq32122 : (σ x) = (σ y) := by grind
  clear eq32111
  have eq32913 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq32122
       grind)
    | exact superpose eq32122 eq10
    | exact resolve eq10 eq32122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32122
  have eq33030 : x = y := by
    first
    | (have i₁ := eq32913
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq32913
    | exact resolve eq32913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32913
  have eq33039 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq33030
       grind)
    | exact superpose eq33030 eq16
    | exact resolve eq16 eq33030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33030
  have eq33045 : False := by grind
  exact eq33045

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq195 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq206 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq205 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq210 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq211 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq527 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq211 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211
    | exact resolve eq211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211 x y
       grind)
    | exact superpose eq211 eq16
    | (have j1 := eq211 x y
       grind)
    | exact resolve eq16 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq562 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq527 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq527
    | (have j0 := eq527 X0 X1
       grind)
    | exact resolve eq527 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq527
  have eq567 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq562
    | exact resolve eq562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq666 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq567 (τ X1) X0
       grind)
    | exact superpose eq567 eq18
    | (have j1 := eq567 (τ X1) X0
       grind)
    | exact resolve eq18 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq567
  have eq869 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq924 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq869 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq869
    | (have j0 := eq869 X0 X1
       grind)
    | exact resolve eq869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq1000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq924 y x
       grind)
    | exact superpose eq924 eq541
    | (have j1 := eq924 (σ y) (σ x)
       grind)
    | (have r₁ := eq541
       have r₂ := eq924 y x
       grind)
    | exact resolve eq541 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1000
  have eq1040 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1001
  have eq1056 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq541
       have i₂ := eq1040
       grind)
    | exact superpose eq1040 eq541
    | exact resolve eq541 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq1040
  have eq1057 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1056
  have eq1058 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1057
  have eq1106 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1058
  have eq1124 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1106
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1106
    | exact resolve eq1106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106
  have eq1129 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1124
       grind)
    | exact superpose eq1124 eq16
    | exact resolve eq16 eq1124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1219 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq924 y x
       grind)
    | exact superpose eq924 eq1129
    | (have j1 := eq924 y x
       grind)
    | (have r₁ := eq1129
       have r₂ := eq924 y x
       grind)
    | exact resolve eq1129 eq924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq1220 : y = (M.op x x) := by grind
  clear eq1219
  have eq1225 : (M.op x y) = (k y x) := by grind
  clear eq1220
  have eq1284 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq1225
       grind)
    | exact superpose eq1225 eq1129
    | exact resolve eq1129 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129 eq1225
  have eq1287 : False := by grind
  exact eq1287

/-- `Equation2736`: `x = ((y ◇ y) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2736 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq62 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | (have j0 := eq61 X0
       grind)
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq326 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq62
    | exact resolve eq62 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq349 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq326 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq326
    | (have j0 := eq326 X0
       grind)
    | exact resolve eq326 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq350 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq349 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq349
    | (have j0 := eq349 (σ X0)
       grind)
    | exact resolve eq349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq442 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq476 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq442
    | (have j0 := eq442 X0 X1
       grind)
    | exact resolve eq442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq880 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq202
       have i₂ := eq476 y x
       grind)
    | exact superpose eq476 eq202
    | (have j1 := eq476 (σ x) (σ y)
       grind)
    | (have r₁ := eq202
       have r₂ := eq476 y x
       grind)
    | (have r₁ := eq202
       have r₂ := eq476 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq202
       have r₂ := eq476 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq202 eq476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq476
  have eq881 : x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq880
  have eq7863 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    grind
  clear eq350
  have eq7878 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7863 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq7863
    | (have j0 := eq7863 X0
       grind)
    | exact resolve eq7863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7863
  have eq14649 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq881
       grind)
    | exact superpose eq881 eq16
    | exact resolve eq16 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq27057 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (τ (σ (σ (k X0 X0)))) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq7878 X0
       grind)
    | exact superpose eq7878 eq10
    | (have j1 := eq7878 X0
       grind)
    | exact resolve eq10 eq7878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7878
  have eq27180 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27057 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq27057
    | (have j0 := eq27057 X0
       grind)
    | exact resolve eq27057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27057
  have eq27181 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq27180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27180
  have eq27436 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq27181 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27181
    | exact resolve eq27181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27526 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq27582 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq27526 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq27526
    | exact resolve eq27526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27526
  have eq27651 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq27436 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq27436
    | exact resolve eq27436 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq27436
  have eq27680 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq27651 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27651
    | exact resolve eq27651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27651
  have eq30988 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq27582 X0
       have i₂ := eq27680 X0
       grind)
    | exact superpose eq27680 eq27582
    | exact resolve eq27582 eq27680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27582
  have eq31099 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq30988
  have eq2538133 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq14649
       have i₂ := eq27181 x
       grind)
    | exact superpose eq27181 eq14649
    | exact resolve eq14649 eq27181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14649
  have eq2538322 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2538133
       have i₂ := eq27680 x
       grind)
    | exact superpose eq27680 eq2538133
    | exact resolve eq2538133 eq27680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538133
  have eq2538323 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq2538322
  have eq2538425 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2538323
       have i₂ := eq27680 x
       grind)
    | exact superpose eq27680 eq2538323
    | exact resolve eq2538323 eq27680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538323
  have eq2538855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq31099 x
       have i₂ := eq2538425
       grind)
    | exact superpose eq2538425 eq31099
    | exact resolve eq31099 eq2538425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538425
  have eq2538980 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2538855
       have r₂ := eq16
       grind)
    | exact resolve eq2538855 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538855
  have eq2544331 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2538980
       grind)
    | exact superpose eq2538980 eq10
    | exact resolve eq10 eq2538980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538980
  have eq2545241 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2544331
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2544331
    | exact resolve eq2544331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544331
  have eq2546069 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2545241
       grind)
    | exact superpose eq2545241 eq16
    | exact resolve eq16 eq2545241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545241
  have eq2546070 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2546069
       have i₂ := eq27181 x
       grind)
    | exact superpose eq27181 eq2546069
    | exact resolve eq2546069 eq27181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27181 eq2546069
  have eq2546071 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2546070
       have i₂ := eq27680 x
       grind)
    | exact superpose eq27680 eq2546070
    | exact resolve eq2546070 eq27680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27680 eq2546070
  have eq2546072 : (σ y) = (σ (M.op x x)) := by grind
  clear eq2546071
  have eq2550516 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2546072
       grind)
    | exact superpose eq2546072 eq10
    | exact resolve eq10 eq2546072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546072
  have eq2551426 : y = (M.op x x) := by
    first
    | (have i₁ := eq2550516
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2550516
    | exact resolve eq2550516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550516
  have eq2552794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31099 x
       have i₂ := eq2551426
       grind)
    | exact superpose eq2551426 eq31099
    | exact resolve eq31099 eq2551426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31099 eq2551426
  have eq2552866 : False := by grind
  exact eq2552866

/-- `Equation2739`: `x = ((y ◇ y) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pyx_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2739 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2739.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : x ≠ x ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq55 eq13
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq55
       grind)
    | exact resolve eq13 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq72 : x = (k x (M.op x y)) := by grind
  clear eq68
  have eq73 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq63 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq63
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq82 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq79
  have eq83 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq85 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq83 (σ X0)
       grind)
    | exact superpose eq83 eq10
    | exact resolve eq10 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq85
    | exact resolve eq85 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq73
    | exact resolve eq73 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq117
    | exact resolve eq117 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq72 eq46
    | exact resolve eq46 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq120 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq119
    | exact resolve eq119 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq126 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq127 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq131 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq127
    | exact resolve eq127 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq133 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq131
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq131
    | exact resolve eq131 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq140 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq126
       grind)
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq50
    | exact resolve eq50 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq207 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq206
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq206
    | exact resolve eq206 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq730 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) (σ X1)
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq54
    | (have j1 := eq99 X0 X1
       grind)
    | exact resolve eq54 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq13188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq13188
    | exact resolve eq13188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13188
  have eq13200 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq13189
       have r₂ := eq28
       grind)
    | exact resolve eq13189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13189
  have eq13233 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq13200 eq54
    | exact resolve eq54 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13239 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq13200 eq91
    | exact resolve eq91 eq13200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq13200
  have eq13253 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13233
    | exact resolve eq13233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13233
  have eq13257 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq13253
       grind)
    | exact superpose eq13253 eq54
    | exact resolve eq54 eq13253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13261 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73 y x
       have i₂ := eq13253
       grind)
    | exact superpose eq13253 eq73
    | exact resolve eq73 eq13253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13253
  have eq13277 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13257
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13257
    | exact resolve eq13257 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13257
  have eq13285 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13277 eq82
    | exact resolve eq82 eq13277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq13277
  have eq13319 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq126
       have i₂ := eq13261
       grind)
    | exact superpose eq13261 eq126
    | exact resolve eq126 eq13261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq13330 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq730 y x
       have i₂ := eq13261
       grind)
    | exact superpose eq13261 eq730
    | (have j0 := eq730 x y
       grind)
    | exact resolve eq730 eq13261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq13261
  have eq13335 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13330
       have i₂ := eq88 y
       grind)
    | exact superpose eq88 eq13330
    | exact resolve eq13330 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq13330
  have eq13345 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13319
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13319
    | exact resolve eq13319 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13319
  have eq13347 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13335
       have i₂ := eq133
       grind)
    | exact superpose eq133 eq13335
    | exact resolve eq13335 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq13335
  have eq13353 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13347
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13347
    | exact resolve eq13347 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13347
  have eq13360 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13353
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13353
    | exact resolve eq13353 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13353
  have eq13364 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13360
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13360
    | exact resolve eq13360 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13360
  have eq13365 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13364
  have eq13369 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13365
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13365
    | exact resolve eq13365 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13365
  have eq13376 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13369
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13369
    | exact resolve eq13369 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13369
  have eq13377 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13376
    | exact resolve eq13376 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13376
  have eq13378 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq13377
  have eq13718 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13285 eq140
    | exact resolve eq140 eq13285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq13285
  have eq13741 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq13718
    | exact resolve eq13718 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13718
  have eq13762 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13345 eq11
    | (have j0 := eq11 (σ y) (M.op (σ y) (σ x))
       grind)
    | exact resolve eq11 eq13345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13345
  have eq13763 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13762
  have eq13765 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13763
    | exact resolve eq13763 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13763
  have eq13766 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13765
  have eq13895 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq13378 eq64
    | exact resolve eq64 eq13378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq13378
  have eq14399 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq13741
       grind)
    | exact superpose eq13741 eq11
    | (have j0 := eq11 y (M.op y x)
       grind)
    | exact resolve eq11 eq13741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13741
  have eq14400 : y = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq14399
  have eq14402 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14400
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14400
    | exact resolve eq14400 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14400
  have eq14403 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq14402
  have eq14824 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq14403
       grind)
    | exact superpose eq14403 eq54
    | exact resolve eq54 eq14403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15488 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq13239 eq118
    | exact resolve eq118 eq13239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq13239
  have eq15502 : x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq15488
  have eq15626 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq15502
       grind)
    | exact superpose eq15502 eq54
    | exact resolve eq54 eq15502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15502
  have eq15648 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15626
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15626
    | exact resolve eq15626 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15626
  have eq15650 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15648 eq30
    | exact resolve eq30 eq15648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15648
  have eq15752 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq15650
    | exact resolve eq15650 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15753 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq15752
  have eq15811 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq15753 eq29
    | exact resolve eq29 eq15753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15813 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15753 eq40
    | exact resolve eq40 eq15753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq15753
  have eq15938 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq42 eq15813
    | exact resolve eq15813 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq15813
  have eq15940 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq15811
    | exact resolve eq15811 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15811
  have eq16066 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15940 eq21
    | exact resolve eq21 eq15940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15940
  have eq16175 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16066
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16066
    | exact resolve eq16066 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16066
  have eq16205 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16175 eq37
    | exact resolve eq37 eq16175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq16175
  have eq16337 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq16205
    | exact resolve eq16205 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq16205
  have eq42271 : (σ x) = (σ (k x x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq72 eq15938
    | exact resolve eq15938 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq15938
  have eq42469 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42271
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq42271
    | exact resolve eq42271 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq42271
  have eq42483 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42469
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq42469
    | exact resolve eq42469 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq42469
  have eq42489 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq42483
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq42483
    | exact resolve eq42483 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42483
  have eq42494 : (τ (σ x)) = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq42489 eq207
    | exact resolve eq207 eq42489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42489
  have eq42763 : x = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq42494
    | exact resolve eq42494 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42494
  have eq43257 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) x) x) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 x
       have i₂ := eq42763
       grind)
    | exact superpose eq42763 eq14
    | exact resolve eq14 eq42763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42763
  have eq79475 : ∀ X0 : G, (σ (M.op x y)) = (σ (k y (M.op (M.op x y) X0))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16337 (M.op sF0 x)
       have i₂ := eq73 sF0 x
       grind)
    | exact superpose eq73 eq16337
    | exact resolve eq16337 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16337
  have eq79844 : ∀ X0 : G, (σ (M.op x y)) = (σ (k y (M.op (M.op x y) X0))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq79475
    | (have j0 := eq79475 X0
       grind)
    | exact resolve eq79475 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79475
  have eq80246 : ∀ X0 : G, (k (σ x) (σ (M.op x y))) = (σ (k x (k y (M.op (M.op x y) X0)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq79844 eq36
    | exact resolve eq36 eq79844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq79844
  have eq80345 : ∀ X0 : G, (σ x) = (σ (k x (k y (M.op (M.op x y) X0)))) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq120 eq80246
    | exact resolve eq80246 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq80246
  have eq139508 : x = (M.op (M.op y x) x) ∨ x = y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43257 y
       have i₂ := eq14824
       grind)
    | exact superpose eq14824 eq43257
    | exact resolve eq43257 eq14824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14824 eq43257
  have eq139615 : x = (M.op (M.op y x) x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq139508
  have eq339924 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13766 eq13895
    | exact resolve eq13895 eq13766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13895
  have eq340003 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq339924
  have eq340510 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq340003 eq54
    | exact resolve eq54 eq340003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq340003
  have eq764124 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq139615
       have i₂ := eq14403
       grind)
    | exact superpose eq14403 eq139615
    | exact resolve eq139615 eq14403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139615
  have eq764254 : x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq764124
  have eq764270 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14403
       have i₂ := eq764254
       grind)
    | exact superpose eq764254 eq14403
    | exact resolve eq14403 eq764254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14403 eq764254
  have eq764418 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq764270
  have eq764455 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq764418 eq30
    | exact resolve eq30 eq764418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764418
  have eq765099 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq764455
    | exact resolve eq764455 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764455
  have eq765100 : y = (M.op x y) ∨ x = y := by grind
  clear eq765099
  have eq765615 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq765100 eq21
    | exact resolve eq21 eq765100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765963 : ∀ X0 : G, (σ x) = (σ (k x (k y (M.op y X0)))) ∨ x = y ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq765100 eq80345
    | exact resolve eq80345 eq765100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80345 eq765100
  have eq766042 : ∀ X0 : G, (σ x) = (σ (k x (k y (M.op y X0)))) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq765963 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765963
  have eq766134 : (σ x) = (σ (k x y)) ∨ x = y := by
    first
    | (have i₁ := eq766042 x
       have i₂ := eq73 y x
       grind)
    | exact superpose eq73 eq766042
    | exact resolve eq766042 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq766042
  have eq766293 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq765615
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq765615
    | exact resolve eq765615 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765615
  have eq766294 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq766134
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq766134
    | exact resolve eq766134 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq766134
  have eq768815 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq766294 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq766294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766294
  have eq768893 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq768815
    | exact resolve eq768815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768815
  have eq1271464 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq768893 eq13766
    | exact resolve eq13766 eq768893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13766 eq768893
  have eq1271662 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1271464
  have eq1272618 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1271662 eq28
    | exact resolve eq28 eq1271662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271662
  have eq1273618 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1272618
       have r₂ := eq766293
       grind)
    | exact resolve eq1272618 eq766293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766293 eq1272618
  have eq1274064 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1273618 eq340510
    | exact resolve eq340510 eq1273618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340510
  have eq1274293 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1274064
  have eq1274649 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1274293
    | exact resolve eq1274293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274293
  have eq1276138 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1274649 eq1273618
    | exact resolve eq1273618 eq1274649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273618 eq1274649
  have eq1276139 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1276138
  have eq1276634 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1276139 eq30
    | exact resolve eq30 eq1276139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1276139
  have eq1277896 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1276634
    | exact resolve eq1276634 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1276634
  have eq1277897 : x = y := by grind
  clear eq1277896
  have eq1278085 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1277897
       grind)
    | exact superpose eq1277897 eq19
    | exact resolve eq19 eq1277897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1278086 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1277897
       grind)
    | exact superpose eq1277897 eq25
    | exact resolve eq25 eq1277897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1277897
  have eq1278478 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1278086
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1278086
    | exact resolve eq1278086 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1278086
  have eq1279895 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1278478 eq27
    | exact resolve eq27 eq1278478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1278478
  have eq1283040 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1279895 eq207
    | exact resolve eq207 eq1279895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq1279895
  have eq1284699 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1283040
       have i₂ := eq1278085
       grind)
    | exact superpose eq1278085 eq1283040
    | exact resolve eq1283040 eq1278085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278085 eq1283040
  have eq1284956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1284699 eq15
    | exact resolve eq15 eq1284699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284699
  have eq1285615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1284956
    | exact resolve eq1284956 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1284956
  have eq1285774 : False := by grind
  exact eq1285774

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pxx_pyx_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq62 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62
    | (have j0 := eq62 x y
       grind)
    | exact resolve eq62 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq62
    | (have j0 := eq62 (σ x) (σ y)
       grind)
    | exact resolve eq62 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 X0) X1
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq63 eq62
    | exact resolve eq62 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq66 (M.op X0 X0) X1
       grind)
    | exact superpose eq66 eq14
    | exact resolve eq14 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq66 (M.op X1 X1) X0
       grind)
    | exact superpose eq66 eq67
    | exact resolve eq67 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq67 (M.op X0 X0) X0
       grind)
    | exact superpose eq67 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq67 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq125 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq97 X1 X0
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq97 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq97 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq97 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq97 X1 X1
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq150 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq214 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq150
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq150
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq223 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq214
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq214
    | exact resolve eq214 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq224 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq223
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq225 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq224
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq224
    | exact resolve eq224 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq298 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq114 X1 (τ X0)
       grind)
    | exact superpose eq114 eq34
    | exact resolve eq34 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq308 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq298
    | exact resolve eq298 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq333 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq612 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq333 X0 (M.op X1 X1)
       have i₂ := eq114 X1 (σ X0)
       grind)
    | exact superpose eq114 eq333
    | exact resolve eq333 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq333
  have eq635 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq612
    | exact resolve eq612 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq3838 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq308 (σ (M.op X1 X1)) X1
       have i₂ := eq142 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq142 eq308
    | (have j1 := eq142 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq308 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq308
  have eq3889 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3838 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838
  have eq4081 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq67 X2 x
       have i₂ := eq3889 x X0
       grind)
    | exact superpose eq3889 eq67
    | exact resolve eq67 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4084 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 x
       have i₂ := eq3889 x X0
       grind)
    | exact superpose eq3889 eq105
    | exact resolve eq105 eq3889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq3889
  have eq22320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq225 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq22321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq22320
    | exact resolve eq22320 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22320
  have eq22326 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq22321
       have r₂ := eq27
       grind)
    | exact resolve eq22321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22321
  have eq22328 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq22326
    | exact resolve eq22326 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22326
  have eq22386 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq22328 eq62
    | exact resolve eq62 eq22328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22328
  have eq22392 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq64 eq22386
    | exact resolve eq22386 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22386
  have eq22409 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq22392 eq635
    | exact resolve eq635 eq22392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq22392
  have eq22476 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq22409
    | exact resolve eq22409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22409
  have eq22477 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq22476 X0
       have j1 := eq125 X0 x X0
       grind)
    | (have r₁ := eq22476 (M.op X0 X0)
       have r₂ := eq125 X0 (k (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq22476 X0
       have r₂ := eq125 x (M.op x y) x
       grind)
    | (have r₁ := eq22476 X0
       have r₂ := eq125 x x x
       grind)
    | exact resolve eq22476 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq22476
  have eq22543 : ∀ X0 : G, x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 x x
       have i₂ := eq22477 X0
       grind)
    | (have i₁ := eq62 X0 x
       have i₂ := eq22477 (M.op X0 x)
       grind)
    | exact superpose eq22477 eq62
    | (have j1 := eq22477 X0
       grind)
    | exact resolve eq62 eq22477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq22477
  have eq22548 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq63 eq22543
    | (have j0 := eq22543 X0
       grind)
    | exact resolve eq22543 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq22543
  have eq22617 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq22548 x
       grind)
    | exact superpose eq22548 eq103
    | (have j0 := eq103 x
       grind)
    | exact resolve eq103 eq22548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq22548
  have eq22638 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22617
  have eq22938 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq67 X0 x
       have i₂ := eq22638
       grind)
    | exact superpose eq22638 eq67
    | exact resolve eq67 eq22638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq22638
  have eq23770 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq22938 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22938
    | (have j0 := eq22938 y
       grind)
    | exact resolve eq22938 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22938
  have eq23870 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq23770 eq29
    | exact resolve eq29 eq23770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq23770
  have eq23918 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq23870
    | exact resolve eq23870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23870
  have eq23919 : y = (M.op x y) ∨ x = y := by grind
  clear eq23918
  have eq23920 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq23919 eq20
    | exact resolve eq20 eq23919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23924 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq23919 eq71
    | exact resolve eq71 eq23919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq23919
  have eq24042 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23920
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23920
    | exact resolve eq23920 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23920
  have eq24393 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq4084 y X0
       have i₂ := eq23924
       grind)
    | exact superpose eq23924 eq4084
    | exact resolve eq4084 eq23924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4084 eq23924
  have eq24427 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24393 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24393
    | (have j0 := eq24393 X0
       grind)
    | exact resolve eq24393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24393
  have eq25485 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq64 eq24427
    | exact resolve eq24427 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq24427
  have eq25597 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq25485 eq27
    | exact resolve eq27 eq25485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25485
  have eq25599 : x = y := by
    first
    | (have r₁ := eq25597
       have r₂ := eq24042
       grind)
    | exact resolve eq25597 eq24042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24042 eq25597
  have eq25601 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25599
       grind)
    | exact superpose eq25599 eq18
    | exact resolve eq18 eq25599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25602 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq25599
       grind)
    | exact superpose eq25599 eq24
    | exact resolve eq24 eq25599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25599
  have eq25723 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25602
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25602
    | exact resolve eq25602 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25602
  have eq25725 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25723 eq26
    | exact resolve eq26 eq25723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq25723
  have eq25784 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq25601
       have i₂ := eq97 X0 x
       grind)
    | (have i₁ := eq25601
       have i₂ := eq97 x X0
       grind)
    | exact superpose eq97 eq25601
    | exact resolve eq25601 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq25601
  have eq26016 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25725 eq25784
    | exact resolve eq25784 eq25725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25725
  have eq26116 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4081 X0 (σ (M.op X0 X0))
       have i₂ := eq25784 (σ (M.op X0 X0))
       grind)
    | exact superpose eq25784 eq4081
    | exact resolve eq4081 eq25784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4081
  have eq26155 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq26116 x
       have i₂ := eq25784 x
       grind)
    | exact superpose eq25784 eq26116
    | exact resolve eq26116 eq25784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25784 eq26116
  have eq26240 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq26155
    | exact resolve eq26155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq26155
  have eq26277 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq26016 eq27
    | exact resolve eq27 eq26016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq26016
  have eq26286 : False := by grind
  exact eq26286

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pxy_y_pyx_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2755 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X0) X1
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq65 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq58 (M.op X0 X0) X1
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 (M.op X0 (M.op X1 X1)) X1
       have i₂ := eq58 (M.op X1 X1) X0
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq82 (M.op X0 X0) X0
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq82 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq148 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 X1
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq145
    | exact resolve eq145 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq145
  have eq152 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq153 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq187 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq199 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq152
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq152
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq207 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq199
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq199
    | exact resolve eq199 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq208 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq207
    | exact resolve eq207 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq212 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq153
       grind)
    | exact superpose eq153 eq16
    | exact resolve eq16 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq304 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 (M.op X1 X1)
       have i₂ := eq148 X1 (τ X0)
       grind)
    | exact superpose eq148 eq35
    | exact resolve eq35 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq314 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq304
    | exact resolve eq304 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq342 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq39
  have eq424 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq118 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq118 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k X0 X0)) (M.op X1 X2)) X1) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) X1
       have i₂ := eq118 X0 X0
       grind)
    | exact superpose eq118 eq14
    | (have j1 := eq118 X0 X0
       grind)
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq434 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq118 X0 X1
       grind)
    | exact superpose eq118 eq54
    | (have j1 := eq118 X0 X1
       grind)
    | exact resolve eq54 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq118 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq438 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq437 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq446 : ∀ X0 : G, (σ X0) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq447 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k X0 X0)) (M.op X1 X2)) X1) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq425 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq448 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq424 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq452 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq446 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq446
    | (have j0 := eq446 X0
       grind)
    | exact resolve eq446 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq453 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq448 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq448 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq448 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq565 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 (M.op X1 X1)
       have i₂ := eq148 X1 (σ X0)
       grind)
    | exact superpose eq148 eq342
    | exact resolve eq342 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq586 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq565
    | exact resolve eq565 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq3211 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq453 (M.op X0 X0) X1
       have i₂ := eq148 X0 (M.op X0 X0)
       grind)
    | exact superpose eq148 eq453
    | (have j0 := eq453 (M.op X0 X0) X1
       grind)
    | exact resolve eq453 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq453
  have eq3235 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq3250 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3235 X0 X1
       have i₂ := eq314 X1 X0
       grind)
    | exact superpose eq314 eq3235
    | exact resolve eq3235 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq3235
  have eq3272 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3250 X1 (M.op (σ (M.op X1 X1)) X0)
       have i₂ := eq54 (σ (M.op X1 X1)) X0
       grind)
    | exact superpose eq54 eq3250
    | exact resolve eq3250 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3642 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq187
    | (have j0 := eq187 x
       grind)
    | exact resolve eq187 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq3650 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3642
  have eq3654 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3650
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3650
    | exact resolve eq3650 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650
  have eq3666 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq3654
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq3654 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654
  have eq3670 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq3666 eq50
    | exact resolve eq50 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3674 : ∀ X0 : G, (k x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3670
       have i₂ := eq80 X0 sF2
       grind)
    | (have i₁ := eq3670
       have i₂ := eq80 sF2 x
       grind)
    | exact superpose eq80 eq3670
    | exact resolve eq3670 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq3679 : ∀ X0 : G, (k X0 (k x x)) = X0 := by
    intro X0
    first
    | exact superpose eq3670 eq586
    | exact resolve eq586 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq3884 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq227 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq227
    | (have j0 := eq227 y
       grind)
    | exact resolve eq227 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq3891 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3884
  have eq3894 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3891
       have i₂ := eq153
       grind)
    | exact superpose eq153 eq3891
    | exact resolve eq3891 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq3891
  have eq3913 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq3894
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq3894 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894
  have eq3941 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3913 eq212
    | exact resolve eq212 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq3913
  have eq4365 : ∀ X0 : G, (k x x) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3674 (σ (M.op X0 X0))
       have i₂ := eq3250 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq3250 eq3674
    | exact resolve eq3674 eq3250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq4370 : (k x x) = (k y y) := by
    first
    | exact superpose eq3941 eq3674
    | exact resolve eq3674 eq3941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3941
  have eq4417 : ∀ X0 : G, (k x x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4365 X0
       have i₂ := eq16 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq4365
    | exact resolve eq4365 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4365
  have eq4526 : ∀ X1 : G, (M.op (k x x) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq59 X1 x
       have i₂ := eq4417 x
       grind)
    | exact superpose eq4417 eq59
    | exact resolve eq59 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4543 : (k x x) = (τ (k x x)) := by
    first
    | (have i₁ := eq3674 x
       have i₂ := eq4417 x
       grind)
    | exact superpose eq4417 eq3674
    | exact resolve eq3674 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4594 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k X0 X0)) (M.op X1 X2)) X1) = X2 ∨ (σ X0) = (k x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq447 X0 X1 X2
       have i₂ := eq4417 (σ X0)
       grind)
    | exact superpose eq4417 eq447
    | (have j0 := eq447 X0 X1 X2
       grind)
    | exact resolve eq447 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq4697 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq4594 X1 X0 (σ (k X1 X1))
       have i₂ := eq58 (σ (k X1 X1)) X0
       grind)
    | exact superpose eq58 eq4594
    | (have j0 := eq4594 X1 X1 x
       grind)
    | exact resolve eq4594 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4594
  have eq5618 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq452 X0
       have j1 := eq438 X0
       grind)
    | (have r₁ := eq452 X0
       have r₂ := eq438 X0
       grind)
    | exact resolve eq452 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq5619 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq5618 X0
       have i₂ := eq4417 (σ X0)
       grind)
    | exact superpose eq4417 eq5618
    | (have j0 := eq5618 X0
       grind)
    | exact resolve eq5618 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5618
  have eq5964 : ∀ X0 X1 : G, (σ X0) = (k x x) ∨ (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq4417 (σ X1)
       grind)
    | exact superpose eq4417 eq434
    | (have j0 := eq434 X0 X1
       grind)
    | exact resolve eq434 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq5965 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (k x x) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq5964 X0 X1
       have i₂ := eq4417 (σ X1)
       grind)
    | exact superpose eq4417 eq5964
    | (have j0 := eq5964 X0 X1
       grind)
    | exact resolve eq5964 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5964
  have eq6020 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k x x) = (σ (k X0 X0)) ∨ (σ X0) = (k x x) ∨ (σ X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq5965 (k X0 X0) X0
       have i₂ := eq5619 X0
       grind)
    | exact superpose eq5619 eq5965
    | (have j0 := eq5965 (k X0 X0) (k X0 X0)
       have j1 := eq5619 (k X0 X0)
       grind)
    | exact resolve eq5965 eq5619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5619 eq5965
  have eq6164 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k x x) = (σ (k X0 X0)) ∨ (σ X0) = (k x x) := by
    intro X0
    first
    | (have j0 := eq6020 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020
  have eq6250 : ∀ X0 : G, (k x x) = (σ (k X0 X0)) ∨ (k x x) = (σ (k X0 X0)) ∨ (σ X0) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq6164 X0
       have i₂ := eq4417 (σ X0)
       grind)
    | exact superpose eq4417 eq6164
    | (have j0 := eq6164 X0
       grind)
    | exact resolve eq6164 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164
  have eq6251 : ∀ X0 : G, (k x x) = (σ (k X0 X0)) ∨ (σ X0) = (k x x) := by
    intro X0
    first
    | (have j0 := eq6250 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6250
  have eq20162 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X1
       have i₂ := eq4697 X0 X1
       grind)
    | exact superpose eq4697 eq438
    | (have j0 := eq438 X1
       have j1 := eq4697 X0 X1
       grind)
    | exact resolve eq438 eq4697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq4697
  have eq20270 : ∀ X0 X1 : G, (σ X1) = (k x x) ∨ (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq20162 X0 X1
       have i₂ := eq4417 (σ X1)
       grind)
    | exact superpose eq4417 eq20162
    | (have j0 := eq20162 X0 X1
       grind)
    | exact resolve eq20162 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20162
  have eq20271 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 X0) ∨ (σ X1) = (k x x) := by
    intro X0 X1
    first
    | (have j0 := eq20270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20270
  have eq20906 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k x x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20271 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq20271
    | (have r₁ := eq20271 X0 (τ (M.op X0 X0))
       have r₂ := eq15 (M.op X0 X0)
       grind)
    | exact resolve eq20271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20271
  have eq21087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq208 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq21088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq21087
    | exact resolve eq21087 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21087
  have eq21099 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21088
       have r₂ := eq28
       grind)
    | exact resolve eq21088 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21088
  have eq21105 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21099 eq3670
    | exact resolve eq3670 eq21099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670 eq21099
  have eq21177 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq21105
    | exact resolve eq21105 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq21105
  have eq21180 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq20906 y x
       grind)
    | (have r₁ := eq21177
       have r₂ := eq20906 (σ x) (σ x)
       grind)
    | (have r₁ := eq21177
       have r₂ := eq20906 y x
       grind)
    | (have r₁ := eq21177
       have r₂ := eq20906 x x
       grind)
    | exact resolve eq21177 eq20906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21177
  have eq21213 : (τ (σ x)) = (k x x) ∨ y = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21180 eq3674
    | exact resolve eq3674 eq21180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3674 eq21180
  have eq21244 : x = (k x x) ∨ y = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq21213
    | exact resolve eq21213 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21213
  have eq21253 : y = (k x x) ∨ x = (k x x) := by
    first
    | (have j1 := eq20906 y x
       grind)
    | (have r₁ := eq21244
       have r₂ := eq20906 x x
       grind)
    | exact resolve eq21244 eq20906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20906 eq21244
  have eq21258 : (σ y) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq21253
       grind)
    | exact superpose eq21253 eq44
    | exact resolve eq44 eq21253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq21266 : ∀ X0 : G, x = (k x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3679 X0
       have i₂ := eq21253
       grind)
    | exact superpose eq21253 eq3679
    | exact resolve eq3679 eq21253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3679
  have eq21275 : x = (k x x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq4543
       have i₂ := eq21253
       grind)
    | exact superpose eq21253 eq4543
    | exact resolve eq4543 eq21253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4543 eq21253
  have eq21322 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq3666 eq21258
    | exact resolve eq21258 eq3666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666 eq21258
  have eq21338 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq21322
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21322
    | exact resolve eq21322 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21322
  have eq21373 : ∀ X0 : G, x = (M.op X0 X0) ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq21275
       have i₂ := eq4417 X0
       grind)
    | exact superpose eq4417 eq21275
    | exact resolve eq21275 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21390 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (τ y) := by
    intro X0
    first
    | (have i₁ := eq4526 X0
       have i₂ := eq21275
       grind)
    | exact superpose eq21275 eq4526
    | exact resolve eq4526 eq21275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21410 : x = (σ x) ∨ x = (σ x) ∨ y = (τ y) := by
    first
    | (have i₁ := eq6251 x
       have i₂ := eq21275
       grind)
    | exact superpose eq21275 eq6251
    | exact resolve eq6251 eq21275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21275
  have eq21415 : x = (σ x) ∨ y = (τ y) := by grind
  clear eq21410
  have eq21422 : y = (τ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq21415
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21415
    | exact resolve eq21415 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21415
  have eq21788 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq21422
       grind)
    | exact superpose eq21422 eq15
    | exact resolve eq15 eq21422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21422
  have eq21835 : y = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq21788
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21788
    | exact resolve eq21788 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21788
  have eq21842 : (σ x) = (M.op y (M.op (σ x) (σ y))) ∨ x = (σ x) := by
    first
    | exact superpose eq21835 eq65
    | exact resolve eq65 eq21835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21835
  have eq22372 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ y = (τ y) := by
    intro X1
    first
    | (have i₁ := eq3272 X1 x
       have i₂ := eq21373 x
       grind)
    | exact superpose eq21373 eq3272
    | exact resolve eq3272 eq21373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21373
  have eq22463 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ y = (τ y) := by
    intro X1
    first
    | (have i₁ := eq22372 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22372
    | (have j0 := eq22372 X1
       grind)
    | exact resolve eq22372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22372
  have eq23099 : y = (τ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21390 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21390
    | (have j0 := eq21390 y
       grind)
    | exact resolve eq21390 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21390
  have eq23164 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq23099
       grind)
    | exact superpose eq23099 eq15
    | exact resolve eq15 eq23099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23099
  have eq23215 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23164
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23164
    | exact resolve eq23164 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23164
  have eq24347 : y = (τ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq22463
    | (have j0 := eq22463 (σ y)
       grind)
    | exact resolve eq22463 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22463
  have eq24439 : y = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq24347
       grind)
    | exact superpose eq24347 eq15
    | exact resolve eq15 eq24347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24347
  have eq24492 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24439
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24439
    | exact resolve eq24439 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24439
  have eq24495 : (σ (M.op x y)) ≠ (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq24492 eq28
    | exact resolve eq28 eq24492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24497 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq24492 eq65
    | exact resolve eq65 eq24492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq24492
  have eq24798 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq24497 eq59
    | exact resolve eq59 eq24497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24497
  have eq56452 : ∀ X0 : G, x = (σ x) ∨ x = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq6251 x
       have i₂ := eq21266 X0
       grind)
    | exact superpose eq21266 eq6251
    | (have j1 := eq21266 X0
       grind)
    | exact resolve eq6251 eq21266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6251 eq21266
  have eq56457 : ∀ X0 : G, x = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq56452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56452
  have eq56464 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq56457 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56457
    | (have j0 := eq56457 X0
       grind)
    | exact resolve eq56457 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56457
  have eq56514 : y = (k x x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq56464 y
       have i₂ := eq4370
       grind)
    | exact superpose eq4370 eq56464
    | exact resolve eq56464 eq4370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4370 eq56464
  have eq57330 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq4526 X0
       have i₂ := eq56514
       grind)
    | exact superpose eq56514 eq4526
    | exact resolve eq4526 eq56514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56514
  have eq59860 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63 eq57330
    | exact resolve eq57330 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59884 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq21842
       have i₂ := eq57330 sF4
       grind)
    | exact superpose eq57330 eq21842
    | exact resolve eq21842 eq57330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21842 eq57330
  have eq59944 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq59884
  have eq59957 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59860 eq27
    | exact resolve eq27 eq59860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59860
  have eq60084 : (σ (M.op x y)) ≠ (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq59944 eq28
    | exact resolve eq28 eq59944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96745 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq21338 eq58
    | exact resolve eq58 eq21338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq21338
  have eq96754 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq96745
    | exact resolve eq96745 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96745
  have eq96770 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq96754
       have i₂ := eq4417 X0
       grind)
    | exact superpose eq4417 eq96754
    | exact resolve eq96754 eq4417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417
  have eq96798 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4526 X0
       have i₂ := eq96754
       grind)
    | exact superpose eq96754 eq4526
    | exact resolve eq4526 eq96754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4526 eq96754
  have eq96989 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq3272 X1 x
       have i₂ := eq96770 x
       grind)
    | exact superpose eq96770 eq3272
    | exact resolve eq3272 eq96770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3272 eq96770
  have eq97136 : ∀ X1 : G, (M.op (σ x) X1) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq96989 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq96989
    | (have j0 := eq96989 X1
       grind)
    | exact resolve eq96989 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96989
  have eq98624 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq96798 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96798
    | (have j0 := eq96798 y
       grind)
    | exact resolve eq96798 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96798
  have eq98744 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98624 eq28
    | exact resolve eq28 eq98624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98745 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98624 eq56
    | exact resolve eq56 eq98624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq98624
  have eq102909 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq97136
    | (have j0 := eq97136 (σ y)
       grind)
    | exact resolve eq97136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97136
  have eq103072 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq102909
  have eq111434 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq98745 eq59
    | exact resolve eq59 eq98745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq98745
  have eq116382 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23215 eq111434
    | exact resolve eq111434 eq23215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23215 eq111434
  have eq116509 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq116382 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116382
  have eq128457 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63 eq116509
    | exact resolve eq116509 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq116509
  have eq128592 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128457 eq21
    | exact resolve eq21 eq128457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128844 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128592
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq128592
    | exact resolve eq128592 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128592
  have eq128909 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128844 eq27
    | exact resolve eq27 eq128844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq128997 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128844 eq24495
    | (have r₁ := eq24495
       have r₂ := eq128844
       grind)
    | exact resolve eq24495 eq128844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24495 eq128844
  have eq129034 : y = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq128997
  have eq137593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq128909 eq24798
    | exact resolve eq24798 eq128909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24798 eq128909
  have eq137608 : y = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq137593
       have r₂ := eq28
       grind)
    | exact resolve eq137593 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137593
  have eq138003 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq137608 eq59957
    | exact resolve eq59957 eq137608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59957 eq137608
  have eq138025 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq138003
  have eq138027 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq138025
    | exact resolve eq138025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq138025
  have eq138038 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq138027 eq28
    | exact resolve eq28 eq138027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138027
  have eq138661 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129034 eq138038
    | exact resolve eq138038 eq129034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129034 eq138038
  have eq138662 : y ≠ (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq138661
  have eq138663 : x = (M.op x y) := by
    first
    | (have r₁ := eq138662
       have r₂ := eq128457
       grind)
    | exact resolve eq138662 eq128457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128457 eq138662
  have eq138665 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq138663 eq21
    | exact resolve eq21 eq138663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq138918 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq138665
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq138665
    | exact resolve eq138665 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138665
  have eq139089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq138918 eq60084
    | (have r₁ := eq60084
       have r₂ := eq138918
       grind)
    | exact resolve eq60084 eq138918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60084
  have eq139100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq138918 eq98744
    | (have r₁ := eq98744
       have r₂ := eq138918
       grind)
    | exact resolve eq98744 eq138918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98744
  have eq139108 : y = (M.op x y) := by grind
  clear eq139100
  have eq139109 : x = (σ (M.op x y)) := by grind
  clear eq139089
  have eq139115 : x = y := by
    first
    | exact superpose eq138663 eq139108
    | exact resolve eq139108 eq138663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138663 eq139108
  have eq139891 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq139115
       grind)
    | exact superpose eq139115 eq25
    | exact resolve eq25 eq139115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq139115
  have eq140216 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq139891
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq139891
    | exact resolve eq139891 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq139891
  have eq140344 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq138918 eq140216
    | exact resolve eq140216 eq138918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140216
  have eq140471 : x = (σ y) := by
    first
    | exact superpose eq139109 eq140344
    | exact resolve eq140344 eq139109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139109 eq140344
  have eq140885 : x ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq140471 eq103072
    | exact resolve eq103072 eq140471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103072 eq140471
  have eq140897 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq140885
       have r₂ := eq59944
       grind)
    | exact resolve eq140885 eq59944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59944 eq140885
  have eq140996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq138918 eq140897
    | exact resolve eq140897 eq138918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138918 eq140897
  have eq141063 : False := by grind
  exact eq141063

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq45
  have eq49 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq52 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq49
  have eq53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq52
  have eq57 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq28 eq57
    | (have j0 := eq57 (σ x) (σ y)
       grind)
    | exact resolve eq57 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X0) X1
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X1) (M.op (M.op X1 X1) X0)
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq59 eq57
    | exact resolve eq57 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq59
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X0 X1
       have i₂ := eq61 (M.op X0 X0) X1
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq194 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq186
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq186
    | exact resolve eq186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq195 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq22 eq194
    | exact resolve eq194 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq218 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq350 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq218
       have i₂ := eq87 X0 sF2
       grind)
    | (have i₁ := eq218
       have i₂ := eq87 sF2 x
       grind)
    | exact superpose eq87 eq218
    | exact resolve eq218 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq218
  have eq383 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ X0)
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq62
    | exact resolve eq62 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq62
  have eq12147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq195 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq12148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq28 eq12147
    | exact resolve eq12147 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12147
  have eq12159 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq12148
       have r₂ := eq29
       grind)
    | exact resolve eq12148 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12148
  have eq12190 : (τ (σ y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12159 eq350
    | exact resolve eq350 eq12159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12159
  have eq12271 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq31 eq12190
    | exact resolve eq12190 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12190
  have eq12272 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq12271
  have eq12349 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq61 x x
       have i₂ := eq12272
       grind)
    | exact superpose eq12272 eq61
    | exact resolve eq61 eq12272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq12272
  have eq12372 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq12349
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq12349
    | exact resolve eq12349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12349
  have eq12413 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq12372 eq31
    | exact resolve eq31 eq12372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq12372
  have eq12520 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq12413
    | exact resolve eq12413 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq12413
  have eq12521 : x = (M.op x y) ∨ x = y := by grind
  clear eq12520
  have eq12679 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12521 eq22
    | exact resolve eq22 eq12521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12681 : y = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12521 eq58
    | exact resolve eq58 eq12521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq12521
  have eq12785 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq12679
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12679
    | exact resolve eq12679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12679
  have eq12990 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq383 x X0
       have i₂ := eq12681
       grind)
    | exact superpose eq12681 eq383
    | exact resolve eq383 eq12681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383 eq12681
  have eq13066 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq12990 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq12990
    | (have j0 := eq12990 X0
       grind)
    | exact resolve eq12990 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12990
  have eq14487 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq68 eq13066
    | exact resolve eq13066 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq13066
  have eq14755 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq14487 eq29
    | exact resolve eq29 eq14487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14487
  have eq14757 : x = y := by
    first
    | (have r₁ := eq14755
       have r₂ := eq12785
       grind)
    | exact resolve eq14755 eq12785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12785 eq14755
  have eq14758 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq14757
       grind)
    | exact superpose eq14757 eq20
    | exact resolve eq20 eq14757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq14759 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq14757
       grind)
    | exact superpose eq14757 eq26
    | exact resolve eq26 eq14757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14757
  have eq14865 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14759
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14759
    | exact resolve eq14759 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14759
  have eq14905 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14865 eq28
    | exact resolve eq28 eq14865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14865
  have eq15453 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq14905 eq350
    | exact resolve eq350 eq14905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq14905
  have eq15531 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq15453
       have i₂ := eq14758
       grind)
    | exact superpose eq14758 eq15453
    | exact resolve eq15453 eq14758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14758 eq15453
  have eq15711 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15531 eq15
    | exact resolve eq15 eq15531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15531
  have eq15750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22 eq15711
    | exact resolve eq15711 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15711
  have eq15761 : False := by grind
  exact eq15761
