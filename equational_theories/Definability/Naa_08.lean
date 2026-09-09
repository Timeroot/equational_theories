import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pxx_pyx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq39
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq351 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq357 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq351 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq361 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq357
    | (have j0 := eq357 X0 X1
       grind)
    | exact resolve eq357 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq362 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq374 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq362 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq362
    | (have j0 := eq362 X0 X1
       grind)
    | exact resolve eq362 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq362
  have eq375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq593 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq375
    | exact resolve eq375 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq375 x y
       grind)
    | exact superpose eq375 eq16
    | (have j1 := eq375 x y
       grind)
    | exact resolve eq16 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq628 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq593
    | (have j0 := eq593 X0 X1
       grind)
    | exact resolve eq593 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq593
  have eq632 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq628
    | (have j0 := eq628 X0 X1
       grind)
    | exact resolve eq628 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq628
  have eq665 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq632 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq632
    | exact resolve eq632 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq753 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq665 (τ X1) X0
       grind)
    | exact superpose eq665 eq18
    | (have j1 := eq665 (τ X1) X0
       grind)
    | exact resolve eq18 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq665
  have eq1226 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq753
    | exact resolve eq753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq1281 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1226 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1226
    | (have j0 := eq1226 X0 X1
       grind)
    | exact resolve eq1226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1393 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq603
       have i₂ := eq1281 y x
       grind)
    | exact superpose eq1281 eq603
    | (have j1 := eq1281 y x
       grind)
    | (have r₁ := eq603
       have r₂ := eq1281 y x
       grind)
    | exact resolve eq603 eq1281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq1394 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1393
  have eq1398 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1394
       grind)
    | exact superpose eq1394 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1394
       grind)
    | exact resolve eq12 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq1405 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1398
  have eq1478 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq619 x y
       have i₂ := eq1405
       grind)
    | exact superpose eq1405 eq619
    | (have j0 := eq619 x y
       grind)
    | exact resolve eq619 eq1405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619 eq1405
  have eq1486 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1478
  have eq1487 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1486
  have eq1568 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1487
       grind)
    | exact superpose eq1487 eq16
    | exact resolve eq16 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1572 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq79 x (σ y)
       have i₂ := eq1487
       grind)
    | exact superpose eq1487 eq79
    | (have j0 := eq79 x (σ y)
       grind)
    | (have r₁ := eq79 x (σ y)
       have r₂ := eq1487
       grind)
    | exact resolve eq79 eq1487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1487
  have eq1583 : (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq1572
  have eq1585 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1583
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1583
    | exact resolve eq1583 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583
  have eq1646 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1281 y x
       have i₂ := eq1585
       grind)
    | exact superpose eq1585 eq1281
    | (have j0 := eq1281 y x
       grind)
    | exact resolve eq1281 eq1585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281 eq1585
  have eq1703 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1646
       have r₂ := eq1568
       grind)
    | exact resolve eq1646 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1803 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1568
       have i₂ := eq1703
       grind)
    | exact superpose eq1703 eq1568
    | exact resolve eq1568 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq1703
  have eq1816 : False := by grind
  exact eq1816

/-- `Equation4294`: `x ◇ (x ◇ y) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | (have i₁ := eq14 X0 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq77
    | exact resolve eq77 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78
    | exact resolve eq78 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq214 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1
       have i₂ := eq14 X0 X1 x
       grind)
    | (have i₁ := eq51 X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq399 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq214
    | (have j0 := eq214 (σ x) (σ y)
       grind)
    | exact resolve eq214 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x
       have i₂ := eq214 x X1
       grind)
    | (have i₁ := eq53 X0 y x
       have i₂ := eq214 X0 X1
       grind)
    | exact superpose eq214 eq53
    | exact resolve eq53 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq444 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq443 x X1
       have i₂ := eq214 x X1
       grind)
    | (have i₁ := eq443 x y
       have i₂ := eq214 x X1
       grind)
    | exact superpose eq214 eq443
    | exact resolve eq443 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq602 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq69 X1 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq612 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq602 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq619 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq612 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq612 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq612 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq629 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq7168 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq629
  have eq7287 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7168
  have eq7288 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq7287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7287
  have eq7729 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7288 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq7288
    | (have j0 := eq7288 x
       grind)
    | exact resolve eq7288 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7742 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq214 (σ X0) (σ X0)
       have i₂ := eq7288 X0
       grind)
    | exact superpose eq7288 eq214
    | exact resolve eq214 eq7288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7761 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq7729
       grind)
    | exact superpose eq7729 eq16
    | exact resolve eq16 eq7729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7729
  have eq8942 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq444 eq7742
    | exact resolve eq7742 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8978 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq8942
       have i₂ := eq7288 (M.op x sF0)
       grind)
    | exact superpose eq7288 eq8942
    | exact resolve eq8942 eq7288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288 eq8942
  have eq8992 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq444 eq8978
    | exact resolve eq8978 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8978
  have eq8999 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq8992 eq16
    | exact resolve eq16 eq8992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq79 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq12151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12150
    | exact resolve eq12150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150
  have eq12164 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq12151
       have r₂ := eq28
       grind)
    | exact resolve eq12151 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12151
  have eq12167 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq12164
    | exact resolve eq12164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12164
  have eq12170 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq12167 eq7761
    | exact resolve eq7761 eq12167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7761 eq12167
  have eq12188 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq12170
    | exact resolve eq12170 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12170
  have eq12189 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12188
  have eq12208 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7742 x
       have i₂ := eq12189
       grind)
    | exact superpose eq12189 eq7742
    | exact resolve eq7742 eq12189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7742
  have eq12215 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq214 x x
       have i₂ := eq12189
       grind)
    | exact superpose eq12189 eq214
    | exact resolve eq214 eq12189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq12189
  have eq12216 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12215
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12215
    | exact resolve eq12215 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12215
  have eq12221 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12208
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq12208
    | exact resolve eq12208 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12208
  have eq12234 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12221
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12221
    | exact resolve eq12221 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq12221
  have eq12235 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12234
    | exact resolve eq12234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12234
  have eq12445 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12216 eq8992
    | exact resolve eq8992 eq12216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12455 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq12445
    | exact resolve eq12445 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12445
  have eq12457 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12455 eq399
    | exact resolve eq399 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12460 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq12457
    | exact resolve eq12457 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12457
  have eq12994 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12235 eq12216
    | exact resolve eq12216 eq12235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12216 eq12235
  have eq13002 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12994
  have eq13009 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13002 eq399
    | exact resolve eq399 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq13011 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq13013 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13009
    | exact resolve eq13009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13009
  have eq14217 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12460 eq444
    | exact resolve eq444 eq12460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14223 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12460 eq8999
    | exact resolve eq8999 eq12460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12460
  have eq14303 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12455 eq14223
    | exact resolve eq14223 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14223
  have eq14336 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq14303
  have eq14338 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq14336
    | exact resolve eq14336 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14336
  have eq14817 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13013 eq444
    | exact resolve eq444 eq13013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14823 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13013 eq8999
    | exact resolve eq8999 eq13013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8999 eq13013
  have eq14906 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13002 eq14823
    | exact resolve eq14823 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14823
  have eq14941 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq14906
  have eq14943 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq14941
       have r₂ := eq13011
       grind)
    | exact resolve eq14941 eq13011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14941
  have eq14944 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq14943
    | exact resolve eq14943 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14943
  have eq14947 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq14944 eq28
    | exact resolve eq28 eq14944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14944
  have eq14967 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq14947
       have r₂ := eq14338
       grind)
    | exact resolve eq14947 eq14338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14338 eq14947
  have eq15372 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12455 eq14217
    | exact resolve eq14217 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455 eq14217
  have eq15386 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15372 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15372
  have eq15431 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13002 eq14817
    | exact resolve eq14817 eq13002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13002 eq14817
  have eq15447 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15431
  have eq15455 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15447 X0
       grind)
    | (have r₁ := eq15447 X0
       have r₂ := eq13011
       grind)
    | exact resolve eq15447 eq13011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13011 eq15447
  have eq15491 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14967 eq15386
    | exact resolve eq15386 eq14967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15386
  have eq15511 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15491 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15491
  have eq15581 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14967 eq15455
    | exact resolve eq15455 eq14967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14967 eq15455
  have eq15601 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq15581 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15581
  have eq16225 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15511 x
       grind)
    | exact superpose eq15511 eq19
    | (have j1 := eq15511 x
       grind)
    | exact resolve eq19 eq15511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15511
  have eq16236 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq16225
  have eq17330 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15601 x
       grind)
    | exact superpose eq15601 eq19
    | (have j1 := eq15601 x
       grind)
    | exact resolve eq19 eq15601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15601
  have eq17341 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17330
  have eq17360 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17341 eq28
    | exact resolve eq28 eq17341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17341
  have eq17384 : y = (M.op x y) := by
    first
    | (have r₁ := eq17360
       have r₂ := eq16236
       grind)
    | exact resolve eq17360 eq16236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16236 eq17360
  have eq17385 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17384 eq21
    | exact resolve eq21 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17436 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17384 eq444
    | exact resolve eq444 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq17453 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq17384 eq8992
    | exact resolve eq8992 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8992
  have eq17457 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq17453
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17453
    | exact resolve eq17453 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17453
  have eq17474 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq17436 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17436
    | (have j0 := eq17436 X0
       grind)
    | exact resolve eq17436 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq17436
  have eq17524 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq17385
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq17385
    | exact resolve eq17385 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq17385
  have eq17526 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq17457
    | exact resolve eq17457 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17457
  have eq17533 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq17384 eq17474
    | exact resolve eq17474 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17474
  have eq17534 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq17384 eq17526
    | exact resolve eq17526 eq17384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17384 eq17526
  have eq17540 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq17524 eq27
    | exact resolve eq27 eq17524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17524
  have eq18224 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq17534 eq17540
    | exact resolve eq17540 eq17534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17540
  have eq18225 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18224
       have i₂ := eq17533 sF2
       grind)
    | exact superpose eq17533 eq18224
    | exact resolve eq18224 eq17533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533 eq18224
  have eq18230 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18225 eq28
    | exact resolve eq28 eq18225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18225
  have eq18260 : False := by grind
  exact eq18260

/-- `Equation437`: `x = x ◇ (y ◇ (y ◇ (x ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pxy_pxy_pyx_Equation437 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq10
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq79 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq22
    | exact resolve eq22 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq32 (τ X0)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq80 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80
    | exact resolve eq80 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq79 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq81
    | exact resolve eq81 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq82
    | exact resolve eq82 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq82
  have eq93 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq89 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq10
    | exact resolve eq10 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X1
       have i₂ := eq100 X1
       grind)
    | exact superpose eq100 eq69
    | (have j0 := eq69 X0 X1
       grind)
    | exact resolve eq69 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq370 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (τ X0))
       have i₂ := eq329 X1 X0
       grind)
    | exact superpose eq329 eq10
    | (have j1 := eq329 X1 X0
       grind)
    | exact resolve eq10 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq391 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq975 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X1 (σ X0)
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq143
    | (have j0 := eq143 X1 (σ X0)
       grind)
    | (have r₁ := eq143 X0 (σ X0)
       have r₂ := eq93 X0
       grind)
    | exact resolve eq143 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq982 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq975 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq975
    | (have j0 := eq975 X0 X1
       grind)
    | exact resolve eq975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1071 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (τ X0)) = (M.op (σ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X1 (τ X0)
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq144
    | (have j0 := eq144 X1 (τ X0)
       grind)
    | exact resolve eq144 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq2005 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X0)) = (τ (M.op X1 X1)) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq391 X1 (τ X0)
       grind)
    | exact superpose eq391 eq33
    | (have j1 := eq391 X1 (τ X0)
       grind)
    | exact resolve eq33 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2015 : ∀ X0 X1 : G, (k (τ (τ X1)) X0) = (τ (M.op (σ X0) (τ X1))) ∨ (M.op (σ X0) (σ X0)) = (τ (M.op X1 X1)) ∨ (M.op (σ X0) (τ X1)) = (M.op (τ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (τ X1) X0
       have i₂ := eq391 X1 (σ X0)
       grind)
    | exact superpose eq391 eq22
    | (have j1 := eq391 X1 (σ X0)
       grind)
    | exact resolve eq22 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq2032 : ∀ X0 X1 : G, (M.op (σ X0) (τ X1)) = (M.op (τ X1) (σ X0)) ∨ (k (τ (τ X1)) X0) = (τ (M.op (σ X0) (τ X1))) ∨ (σ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2015 X0 X1
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq2015
    | (have j0 := eq2015 X0 X1
       grind)
    | exact resolve eq2015 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2015
  have eq2040 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2005 X0 X1
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq2005
    | (have j0 := eq2005 X0 X1
       grind)
    | exact resolve eq2005 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2005
  have eq118353 : ∀ X0 X1 : G, (M.op (σ X0) (τ X1)) ≠ (M.op (σ X0) (τ X1)) ∨ (k (σ X0) (τ X1)) = (M.op (σ X0) (τ X1)) ∨ (k (τ (τ X1)) X0) = (τ (M.op (σ X0) (τ X1))) ∨ (σ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) (τ X1)
       have i₂ := eq2032 X0 X1
       grind)
    | exact superpose eq2032 eq41
    | (have j0 := eq41 (σ X0) (τ X1)
       have j1 := eq2032 X0 X1
       grind)
    | (have r₁ := eq41 (σ X0) (τ X1)
       have r₂ := eq2032 X0 X1
       grind)
    | (have r₁ := eq41 (τ X1) (σ X0)
       have r₂ := eq2032 X0 X1
       grind)
    | exact resolve eq41 eq2032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq118362 : ∀ X0 X1 : G, (k (σ X0) (τ X1)) = (M.op (σ X0) (τ X1)) ∨ (k (τ (τ X1)) X0) = (τ (M.op (σ X0) (τ X1))) ∨ (σ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118353
  have eq118368 : ∀ X0 X1 : G, (k (σ X0) (τ X1)) = (M.op (σ X0) (τ X1)) ∨ (k (τ (τ X1)) X0) = (τ (M.op (σ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq118362 X0 X1
       have j1 := eq1071 X1 X0
       grind)
    | (have r₁ := eq118362 X1 X0
       have r₂ := eq1071 X0 X1
       grind)
    | exact resolve eq118362 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq118362
  have eq118500 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq118368 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118368
    | exact resolve eq118368 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118368
  have eq118915 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq118500 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq118500
    | exact resolve eq118500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118500
  have eq119504 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq118915 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq118915
    | (have j0 := eq118915 X0 X1
       grind)
    | exact resolve eq118915 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118915
  have eq119606 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X1) (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119504 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq119504
    | (have j0 := eq119504 (σ X1) (σ X0)
       grind)
    | exact resolve eq119504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119680 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq119504 X0 X1
       grind)
    | exact superpose eq119504 eq11
    | (have j1 := eq119504 X0 X1
       grind)
    | exact resolve eq11 eq119504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119504
  have eq120047 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq119680 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq119680
    | (have j0 := eq119680 X0 X1
       grind)
    | exact resolve eq119680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119680
  have eq120076 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119606 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq119606
    | (have j0 := eq119606 X0 X1
       grind)
    | exact resolve eq119606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119606
  have eq120100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq120076 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq120076
    | (have j0 := eq120076 X0 X1
       grind)
    | exact resolve eq120076 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120076
  have eq120526 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq120047 (τ X0) X1
       grind)
    | exact superpose eq120047 eq18
    | (have j1 := eq120047 (τ X0) X1
       grind)
    | exact resolve eq18 eq120047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120698 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq120047 (σ X0) (σ X1)
       grind)
    | exact superpose eq120047 eq15
    | (have j1 := eq120047 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq120047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120786 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq120047 (τ X0) (τ X1)
       grind)
    | exact superpose eq120047 eq33
    | (have j1 := eq120047 (τ X0) (τ X1)
       grind)
    | exact resolve eq33 eq120047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120047
  have eq120955 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120786 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq120786
    | (have j0 := eq120786 X0 X1
       grind)
    | exact resolve eq120786 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120786
  have eq120965 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq120698 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq120698
    | (have j0 := eq120698 X0 X1
       grind)
    | exact resolve eq120698 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120698
  have eq123689 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq120526 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq120526
    | exact resolve eq120526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120526
  have eq124110 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq123689 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq123689
    | (have j0 := eq123689 X0 X1
       grind)
    | exact resolve eq123689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123689
  have eq133644 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq120955 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134413 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq133644 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq133644
    | exact resolve eq133644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133644
  have eq134555 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134413 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq134413
    | (have j0 := eq134413 X0 X1
       grind)
    | exact resolve eq134413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq134413
  have eq134688 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134555 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq134555
    | (have j0 := eq134555 X0 X1
       grind)
    | exact resolve eq134555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134555
  have eq134795 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq134688 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq134688
    | (have j0 := eq134688 X0 X1
       grind)
    | (have r₁ := eq134688 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq134688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134688
  have eq134869 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq134795 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq134795
    | (have j0 := eq134795 X0 X1
       grind)
    | exact resolve eq134795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134795
  have eq134918 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq134869 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134869
    | (have j0 := eq134869 X0 X1
       grind)
    | exact resolve eq134869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134869
  have eq134952 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq134918 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq134918
    | (have j0 := eq134918 X0 X1
       grind)
    | exact resolve eq134918 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134918
  have eq135045 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134952 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq134952
    | exact resolve eq134952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134952
  have eq135299 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135045 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq135045
    | (have j0 := eq135045 X0 X1
       grind)
    | (have r₁ := eq135045 X0 X0
       have r₂ := eq15 X0 X0
       grind)
    | exact resolve eq135045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135045
  have eq140177 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq120965 x y
       grind)
    | exact superpose eq120965 eq16
    | (have j1 := eq120965 x y
       grind)
    | exact resolve eq16 eq120965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140344 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (σ X0) (σ X1)
       have i₂ := eq120965 X0 X1
       grind)
    | exact superpose eq120965 eq41
    | (have j1 := eq120965 X1 X0
       grind)
    | exact resolve eq41 eq120965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq120965
  have eq140363 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq140344 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq140344
    | (have j0 := eq140344 X0 X1
       grind)
    | exact resolve eq140344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140344
  have eq140564 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq140363 X0 X1
       have j1 := eq135299 X1 X0
       grind)
    | (have r₁ := eq140363 X0 X1
       have r₂ := eq135299 X0 X1
       grind)
    | (have r₁ := eq140363 X1 X0
       have r₂ := eq135299 X0 X1
       grind)
    | exact resolve eq140363 eq135299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135299 eq140363
  have eq152782 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq140564 X0 X1
       have i₂ := eq120100 X1 X0
       grind)
    | exact superpose eq120100 eq140564
    | (have j0 := eq140564 X0 X1
       have j1 := eq120100 X0 X1
       grind)
    | (have r₁ := eq140564 X1 X0
       have r₂ := eq120100 X0 X1
       grind)
    | exact resolve eq140564 eq120100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120100 eq140564
  have eq152820 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq152782 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152782
  have eq160953 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq152820 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152820
    | exact resolve eq152820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152820
  have eq161524 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq160953 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq160953
    | (have j0 := eq160953 X0 X1
       grind)
    | exact resolve eq160953 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160953
  have eq161854 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq161524 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq161524
    | exact resolve eq161524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161524
  have eq162455 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq161854 X0 X1
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq161854
    | (have j0 := eq161854 X0 X1
       grind)
    | exact resolve eq161854 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161854
  have eq162744 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq162455 X1 X0
       grind)
    | exact superpose eq162455 eq11
    | (have j1 := eq162455 X1 X0
       grind)
    | exact resolve eq11 eq162455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162455
  have eq163126 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq162744 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq162744
    | (have j0 := eq162744 X0 X1
       grind)
    | exact resolve eq162744 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162744
  have eq163916 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq163126 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163126
  have eq164052 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X1 X1)) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq163916 (τ X1) (τ X0)
       have i₂ := eq2040 X1 X0
       grind)
    | exact superpose eq2040 eq163916
    | (have j0 := eq163916 (τ X1) (τ X0)
       have j1 := eq2040 X0 X1
       grind)
    | (have r₁ := eq163916 (τ X1) (τ X0)
       have r₂ := eq2040 X0 X1
       grind)
    | (have r₁ := eq163916 (τ X0) (τ X1)
       have r₂ := eq2040 X0 X1
       grind)
    | exact resolve eq163916 eq2040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040
  have eq164495 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq164052 X0 X1
       have j1 := eq163916 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq164052 X0 X1
       have r₂ := eq163916 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq164052 X0 X1
       have r₂ := eq163916 (τ X0) (τ X1)
       grind)
    | exact resolve eq164052 eq163916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163916 eq164052
  have eq164594 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X0 X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq164495 X0 X1
       have i₂ := eq33 X0 X1
       grind)
    | exact superpose eq33 eq164495
    | (have j0 := eq164495 X0 X1
       grind)
    | exact resolve eq164495 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq164495
  have eq164639 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq164594 X0 X1
       have j1 := eq120955 X0 X1
       grind)
    | (have r₁ := eq164594 X0 X0
       have r₂ := eq120955 X0 X0
       grind)
    | (have r₁ := eq164594 X0 X1
       have r₂ := eq120955 X0 X1
       grind)
    | exact resolve eq164594 eq120955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120955 eq164594
  have eq177583 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq164639 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq164639
    | (have j0 := eq164639 (σ X0) X1
       grind)
    | exact resolve eq164639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164639
  have eq177828 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq177583 X0 X1
       have i₂ := eq29 X0 X1
       grind)
    | exact superpose eq29 eq177583
    | (have j0 := eq177583 X0 X1
       grind)
    | exact resolve eq177583 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq177583
  have eq177891 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq177828 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq177828
    | (have j0 := eq177828 X0 X1
       grind)
    | exact resolve eq177828 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177828
  have eq178011 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq177891 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177891
    | (have j0 := eq177891 X1 (σ X0)
       grind)
    | exact resolve eq177891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177891
  have eq178624 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178011 X0 X1
       have i₂ := eq90 X0
       grind)
    | exact superpose eq90 eq178011
    | (have j0 := eq178011 X0 X1
       grind)
    | exact resolve eq178011 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178011
  have eq178962 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X1
       have i₂ := eq178624 (σ X1) X0
       grind)
    | (have i₁ := eq90 X0
       have i₂ := eq178624 X0 (σ X0)
       grind)
    | exact superpose eq178624 eq90
    | (have j1 := eq178624 (σ X1) X0
       grind)
    | exact resolve eq90 eq178624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178973 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1
       have i₂ := eq178624 (τ X1) X0
       grind)
    | (have i₁ := eq89 X0
       have i₂ := eq178624 X0 (τ X0)
       grind)
    | exact superpose eq178624 eq89
    | (have j1 := eq178624 (τ X1) X0
       grind)
    | exact resolve eq89 eq178624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq178624
  have eq182953 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq178962 (σ X1) X0
       grind)
    | exact superpose eq178962 eq15
    | (have j1 := eq178962 (σ X1) X0
       grind)
    | exact resolve eq15 eq178962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178962
  have eq183275 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182953 X0 X1
       have i₂ := eq90 X1
       grind)
    | exact superpose eq90 eq182953
    | (have j0 := eq182953 X0 X1
       grind)
    | exact resolve eq182953 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq182953
  have eq185470 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq178973 X1 X0
       grind)
    | exact superpose eq178973 eq18
    | (have j1 := eq178973 X1 X0
       grind)
    | exact resolve eq18 eq178973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq178973
  have eq191040 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq183275 x y
       grind)
    | exact superpose eq183275 eq16
    | (have j1 := eq183275 x y
       grind)
    | exact resolve eq16 eq183275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183275
  have eq191293 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq191040
       have i₂ := eq124110 x y
       grind)
    | exact superpose eq124110 eq191040
    | (have j1 := eq124110 x y
       grind)
    | (have r₁ := eq191040
       have r₂ := eq124110 x y
       grind)
    | exact resolve eq191040 eq124110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124110 eq191040
  have eq191297 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq191293
  have eq191303 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq191297
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq191297
       have r₂ := eq12 y x
       grind)
    | exact resolve eq191297 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191297
  have eq258323 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185470 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq185470
    | (have j0 := eq185470 (σ X0) X1
       grind)
    | exact resolve eq185470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185470
  have eq258964 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258323 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq258323
    | (have j0 := eq258323 X0 X1
       grind)
    | exact resolve eq258323 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258323
  have eq258991 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq258964 X0 X1
       have i₂ := eq93 X0
       grind)
    | exact superpose eq93 eq258964
    | (have j0 := eq258964 X0 X1
       grind)
    | exact resolve eq258964 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq258964
  have eq276419 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq140177
       have i₂ := eq258991 x y
       grind)
    | exact superpose eq258991 eq140177
    | (have j1 := eq258991 x y
       grind)
    | (have r₁ := eq140177
       have r₂ := eq258991 x y
       grind)
    | exact resolve eq140177 eq258991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140177 eq258991
  have eq276774 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq276419
  have eq276871 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j1 := eq982 x y
       grind)
    | (have r₁ := eq276774
       have r₂ := eq982 x y
       grind)
    | (have r₁ := eq276774
       have r₂ := eq982 y x
       grind)
    | exact resolve eq276774 eq982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982 eq276774
  have eq277163 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq276871
       have i₂ := eq191303
       grind)
    | exact superpose eq191303 eq276871
    | exact resolve eq276871 eq191303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191303 eq276871
  have eq277218 : False := by grind
  exact eq277218
