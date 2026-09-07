import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1033`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then X else if X = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_x_y_pxy_Equation1033 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1033 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1033.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq25 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X2)) X2
       have i₂ := eq9 X0 x X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0 (M.op X0 x)
       have i₂ := eq25 X0 x
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq27 (σ X0)
       grind)
    | exact superpose eq27 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | (have j0 := eq52 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq52 X0 (τ X1)
       grind)
    | exact superpose eq52 eq19
    | (have j1 := eq52 X0 (τ X1)
       grind)
    | exact resolve eq19 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq233 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq372 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2413 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq186 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq186
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq2459 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2413 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2413
    | (have j0 := eq2413 X0 X1
       grind)
    | exact resolve eq2413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2579 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (τ X0) (τ X1)
       have i₂ := eq233 X1 X0
       grind)
    | exact superpose eq233 eq388
    | (have j0 := eq388 (τ X0) (τ X1)
       grind)
    | exact resolve eq388 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq2608 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2579 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2579
    | (have j0 := eq2579 X0 X1
       grind)
    | exact resolve eq2579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2619 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2608 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2608
    | (have j0 := eq2608 X0 X1
       grind)
    | exact resolve eq2608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2608
  have eq2624 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2619 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2619
    | (have j0 := eq2619 X0 X1
       grind)
    | exact resolve eq2619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq2625 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2624 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2624
    | (have j0 := eq2624 X0 X1
       grind)
    | exact resolve eq2624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq2626 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2625 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2625
    | (have j0 := eq2625 X0 X1
       grind)
    | exact resolve eq2625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2627 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2626 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2626
    | (have j0 := eq2626 X0 X1
       grind)
    | exact resolve eq2626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626
  have eq3457 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq180 x y
       grind)
    | exact superpose eq180 eq16
    | (have j1 := eq180 x y
       grind)
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3724 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq372
       have i₂ := eq52 x y
       grind)
    | exact superpose eq52 eq372
    | (have j1 := eq52 x y
       grind)
    | (have r₁ := eq372
       have r₂ := eq52 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq372
       have r₂ := eq52 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq372 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq372
  have eq3727 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq3724
  have eq52310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq3457
       have i₂ := eq2459 y x
       grind)
    | exact superpose eq2459 eq3457
    | (have j1 := eq2459 y x
       grind)
    | (have r₁ := eq3457
       have r₂ := eq2459 y x
       grind)
    | (have r₁ := eq3457
       have r₂ := eq2459 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3457
       have r₂ := eq2459 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3457 eq2459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459 eq3457
  have eq52313 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by grind
  clear eq52310
  have eq53539 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3727
       grind)
    | exact superpose eq3727 eq16
    | exact resolve eq16 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq53784 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq53539
       have r₂ := eq52313
       grind)
    | exact resolve eq53539 eq52313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52313 eq53539
  have eq53806 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq388 x y
       have i₂ := eq53784
       grind)
    | exact superpose eq53784 eq388
    | (have j0 := eq388 x y
       grind)
    | exact resolve eq388 eq53784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq53809 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2627 x y
       have i₂ := eq53784
       grind)
    | exact superpose eq53784 eq2627
    | (have j0 := eq2627 x y
       grind)
    | (have r₁ := eq2627 x y
       have r₂ := eq53784
       grind)
    | exact resolve eq2627 eq53784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627 eq53784
  have eq53828 : x ≠ x ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq53809
  have eq53829 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq53828
  have eq53832 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq53806
  have eq53833 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq53832
  have eq54931 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq53833
       grind)
    | exact superpose eq53833 eq16
    | exact resolve eq16 eq53833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53833
  have eq55626 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54931
       have i₂ := eq53829
       grind)
    | exact superpose eq53829 eq54931
    | exact resolve eq54931 eq53829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53829 eq54931
  have eq55627 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55626
  have eq55628 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq55627
  have eq55976 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq55628
       grind)
    | exact superpose eq55628 eq10
    | exact resolve eq10 eq55628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55628
  have eq56070 : x = y ∨ x = y := by
    first
    | (have i₁ := eq55976
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55976
    | exact resolve eq55976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55976
  have eq56071 : x = y := by grind
  clear eq56070
  have eq56622 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56071
       grind)
    | exact superpose eq56071 eq16
    | exact resolve eq16 eq56071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56071
  have eq56623 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq56622
       have i₂ := eq27 x
       grind)
    | exact superpose eq27 eq56622
    | exact resolve eq56622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56622
  have eq56624 : False := by grind
  exact eq56624

/-- `Equation1033`: `x = x ◇ ((x ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then X else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_x_x_pxy_Equation1033 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1033 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1033.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X2)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X2)) X2
       have i₂ := eq9 X0 x X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0 (M.op X0 x)
       have i₂ := eq25 X0 x
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq27 (σ X0)
       grind)
    | exact superpose eq27 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) (σ X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq25
    | (have j1 := eq53 X0 X1
       grind)
    | exact resolve eq25 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq2370 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq208 X1 X0
       grind)
    | exact superpose eq208 eq53
    | (have j0 := eq53 X1 X0
       have j1 := eq208 X1 X0
       grind)
    | exact resolve eq53 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq208
  have eq2414 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370
  have eq2481 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2414 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2414
    | exact resolve eq2414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2495 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2414 y x
       grind)
    | exact superpose eq2414 eq16
    | (have j1 := eq2414 x y
       grind)
    | exact resolve eq16 eq2414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq2561 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2481 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2481
    | (have j0 := eq2481 X0 X1
       grind)
    | exact resolve eq2481 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2481
  have eq2700 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2561 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2561
    | exact resolve eq2561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq3168 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2495
       have i₂ := eq2700 x y
       grind)
    | exact superpose eq2700 eq2495
    | (have j1 := eq2700 (σ x) (σ y)
       grind)
    | (have r₁ := eq2495
       have r₂ := eq2700 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2495
       have r₂ := eq2700 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2495 eq2700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495 eq2700
  have eq3169 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3168
  have eq3362 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3169
       grind)
    | exact superpose eq3169 eq10
    | exact resolve eq10 eq3169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3169
  have eq3411 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3362
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3362
    | exact resolve eq3362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3362
  have eq3412 : x = y := by grind
  clear eq3411
  have eq3563 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3412
       grind)
    | exact superpose eq3412 eq16
    | exact resolve eq16 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq3564 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3563
       have i₂ := eq27 x
       grind)
    | exact superpose eq27 eq3563
    | exact resolve eq3563 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563
  have eq3565 : False := by grind
  exact eq3565

/-- `Equation1037`: `x = x ◇ ((y ◇ (x ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then Y else if m(X,X) = X then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_x_y_pxy_x_Equation1037 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law1037 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1037.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq9 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) x)
       have i₂ := eq9 (M.op X0 (M.op X1 X1)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq75 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 X1) X1 x
       have i₂ := eq24 (M.op X1 X1) X1
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X1) ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have r₂ := eq23 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq102 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq75
    | exact resolve eq75 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq107 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq75 X0 (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq24 x (M.op X0 X0)
       grind)
    | exact superpose eq24 eq75
    | exact resolve eq75 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq116 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X1
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq102
    | exact resolve eq102 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq133 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq24
    | exact resolve eq24 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq153 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = X2 ∨ (k X0 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq52 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq169 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = X2 ∨ (k X0 X2) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq153 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq173 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq133 X0
       grind)
    | exact resolve eq13 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq24
    | exact resolve eq24 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq188 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq174 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq315 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       grind)
    | (have r₁ := eq315 X0 X1
       have r₂ := eq133 X0
       grind)
    | exact resolve eq315 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq315
  have eq792 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq813 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq325 (M.op X1 X0) X0
       have i₂ := eq176 X0 X1
       grind)
    | exact superpose eq176 eq325
    | exact resolve eq325 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq884 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 (σ X0)) X0
       have i₂ := eq813 (σ X0) X1
       grind)
    | exact superpose eq813 eq22
    | exact resolve eq22 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq813
  have eq887 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq884
    | exact resolve eq884 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq4455 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (k (σ X0) X2) ∨ (k (σ X0) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq169 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq169 eq15
    | (have j1 := eq169 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq15 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq6621 : ∀ X0 X1 : G, (k (σ (M.op X0 (M.op X0 X0))) X1) = (σ (M.op (M.op X0 (M.op X0 X0)) (τ X1))) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq99 X0 (τ X1)
       grind)
    | exact superpose eq99 eq18
    | (have j1 := eq99 X0 (τ X1)
       grind)
    | exact resolve eq18 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq99
  have eq6663 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6621 X1 X1
       have i₂ := eq176 X1 X1
       grind)
    | exact superpose eq176 eq6621
    | (have j0 := eq6621 X0 X1
       grind)
    | exact resolve eq6621 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6621
  have eq6668 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6663 X1 X1
       have i₂ := eq176 X1 X1
       grind)
    | exact superpose eq176 eq6663
    | (have j0 := eq6663 X0 X1
       grind)
    | exact resolve eq6663 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq6663
  have eq7300 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq188 (σ X0) (σ X1)
       grind)
    | exact superpose eq188 eq15
    | (have j1 := eq188 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9220 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6668 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6668
    | exact resolve eq6668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6668
  have eq9284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9220 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9220
    | (have j0 := eq9220 X0 X1
       grind)
    | exact resolve eq9220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9220
  have eq21510 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ X0) = (k (σ X0) X2) ∨ (k (σ X0) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 (σ X0) (σ X1)
       have i₂ := eq4455 X0 X1 X2
       grind)
    | exact superpose eq4455 eq116
    | (have j1 := eq4455 X0 (k X0 X1) X2
       grind)
    | exact resolve eq116 eq4455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq288466 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7300 x y
       grind)
    | exact superpose eq7300 eq16
    | (have j1 := eq7300 x y
       grind)
    | exact resolve eq16 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288528 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq173 (σ X0) (σ X1)
       have i₂ := eq7300 X0 X1
       grind)
    | exact superpose eq7300 eq173
    | (have j0 := eq173 (σ X0) (σ X1)
       have j1 := eq7300 X0 X1
       grind)
    | (have r₁ := eq173 (σ X0) (σ X1)
       have r₂ := eq7300 X0 X1
       grind)
    | exact resolve eq173 eq7300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7300
  have eq288644 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq288528 X0 X1
       have j1 := eq173 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq288528 X0 X1
       have r₂ := eq173 (σ X0) (σ X1)
       grind)
    | exact resolve eq288528 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288528
  have eq288674 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq288644 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq288644
    | (have j0 := eq288644 X0 X1
       grind)
    | exact resolve eq288644 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288644
  have eq289396 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq288674 (τ X1) (τ X0)
       have i₂ := eq792 X0 X1
       grind)
    | exact superpose eq792 eq288674
    | exact resolve eq288674 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq288674
  have eq289463 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq289396 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq289396
    | (have j0 := eq289396 X0 X1
       grind)
    | exact resolve eq289396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289396
  have eq289479 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq289463 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq289463
    | (have j0 := eq289463 X0 X1
       grind)
    | exact resolve eq289463 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289463
  have eq289482 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq289479 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq289479
    | (have j0 := eq289479 X0 X1
       grind)
    | exact resolve eq289479 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289479
  have eq289484 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq289482 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq289482
    | (have j0 := eq289482 X0 X1
       grind)
    | exact resolve eq289482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289482
  have eq299758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq288466
       have i₂ := eq9284 y x
       grind)
    | exact superpose eq9284 eq288466
    | (have j1 := eq9284 (σ y) (σ x)
       grind)
    | (have r₁ := eq288466
       have r₂ := eq9284 y x
       grind)
    | exact resolve eq288466 eq9284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9284 eq288466
  have eq299759 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq299758
  have eq300398 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq887 y (σ x)
       have i₂ := eq299759
       grind)
    | exact superpose eq299759 eq887
    | exact resolve eq887 eq299759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq299759
  have eq300538 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq300398
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq300398
    | exact resolve eq300398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300398
  have eq300547 : y = (k x y) := by
    first
    | (have j1 := eq173 x y
       grind)
    | (have r₁ := eq300538
       have r₂ := eq173 x y
       grind)
    | exact resolve eq300538 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq300538
  have eq301194 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188 x y
       have i₂ := eq300547
       grind)
    | exact superpose eq300547 eq188
    | (have j0 := eq188 x y
       grind)
    | exact resolve eq188 eq300547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303305 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq116 x y
       have i₂ := eq301194
       grind)
    | exact superpose eq301194 eq116
    | exact resolve eq116 eq301194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301194
  have eq303429 : x = (M.op x y) := by grind
  clear eq303305
  have eq399009 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) X0) ∨ (k (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21510 x y X0
       have i₂ := eq300547
       grind)
    | exact superpose eq300547 eq21510
    | (have j0 := eq21510 x y X0
       grind)
    | exact resolve eq21510 eq300547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21510 eq300547
  have eq400463 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) X0) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq399009 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399009
  have eq400508 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq400463 X0
       have j1 := eq289484 (σ x) X0
       grind)
    | (have r₁ := eq400463 x
       have r₂ := eq289484 (σ x) x
       grind)
    | (have r₁ := eq400463 (σ x)
       have r₂ := eq289484 (σ x) (σ x)
       grind)
    | exact resolve eq400463 eq289484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289484 eq400463
  have eq400569 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq400508 X0
       grind)
    | exact superpose eq400508 eq16
    | (have j1 := eq400508 X0
       grind)
    | exact resolve eq16 eq400508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400508
  have eq400928 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq400569 X0
       have i₂ := eq303429
       grind)
    | exact superpose eq303429 eq400569
    | (have j0 := eq400569 X0
       grind)
    | exact resolve eq400569 eq303429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400569
  have eq400929 : ∀ X0 : G, (k (σ x) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq400928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400928
  have eq401546 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq188 (σ x) X0
       have i₂ := eq400929 X0
       grind)
    | exact superpose eq400929 eq188
    | (have j0 := eq188 (σ x) X0
       grind)
    | exact resolve eq188 eq400929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq400929
  have eq547366 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq116 (σ x) X0
       have i₂ := eq401546 X0
       grind)
    | exact superpose eq401546 eq116
    | (have j1 := eq401546 X0
       grind)
    | exact resolve eq116 eq401546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq401546
  have eq547726 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq547366 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547366
  have eq549080 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq547726 (σ y)
       grind)
    | exact superpose eq547726 eq16
    | exact resolve eq16 eq547726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547726
  have eq549393 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq549080
       have i₂ := eq303429
       grind)
    | exact superpose eq303429 eq549080
    | exact resolve eq549080 eq303429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303429 eq549080
  have eq549394 : False := by grind
  exact eq549394

/-- `Equation1037`: `x = x ◇ ((y ◇ (x ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then Y else if m(X,X) = X then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_x_y_pxy_y_Equation1037 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law1037 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1037.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq9 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) x)
       have i₂ := eq9 (M.op X0 (M.op X1 X1)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq79 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq53 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq87 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X2) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq107 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 X1) X1 x
       have i₂ := eq24 (M.op X1 X1) X1
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X1) ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have r₂ := eq23 X0 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq137 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq107
    | exact resolve eq107 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq142 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 X0 (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq24 x (M.op X0 X0)
       grind)
    | exact superpose eq24 eq107
    | exact resolve eq107 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq152 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq137
    | exact resolve eq137 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq170 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq24
    | exact resolve eq24 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq187 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq170 X0
       grind)
    | exact superpose eq170 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq170 X0
       grind)
    | exact resolve eq13 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq170 X0
       grind)
    | exact superpose eq170 eq24
    | exact resolve eq24 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq295 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq189 X0 X1
       grind)
    | exact superpose eq189 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq295 X0 X1
       have i₂ := eq170 X0
       grind)
    | exact superpose eq170 eq295
    | (have j0 := eq295 X0 X1
       grind)
    | (have r₁ := eq295 X0 X1
       have r₂ := eq170 X0
       grind)
    | exact resolve eq295 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq295
  have eq300 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq299 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq667 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq300 (M.op X1 X0) X0
       have i₂ := eq189 X0 X1
       grind)
    | exact superpose eq189 eq300
    | exact resolve eq300 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 (σ X0)) X0
       have i₂ := eq667 (σ X0) X1
       grind)
    | exact superpose eq667 eq22
    | exact resolve eq22 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq787 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq784 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq784
    | exact resolve eq784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq2123 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq87 (σ X0) (σ X1) X2
       grind)
    | exact superpose eq87 eq15
    | (have j1 := eq87 (σ X0) (σ X1) X2
       grind)
    | exact resolve eq15 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq4159 : ∀ X0 X1 : G, (k (σ (M.op X0 (M.op X0 X0))) X1) = (σ (M.op (M.op X0 (M.op X0 X0)) (τ X1))) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq133 X0 (τ X1)
       grind)
    | exact superpose eq133 eq18
    | (have j1 := eq133 X0 (τ X1)
       grind)
    | exact resolve eq18 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq4162 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4159 X1 X1
       have i₂ := eq189 X1 X1
       grind)
    | exact superpose eq189 eq4159
    | (have j0 := eq4159 X0 X1
       grind)
    | exact resolve eq4159 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4159
  have eq4166 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4162 X1 X1
       have i₂ := eq189 X1 X1
       grind)
    | exact superpose eq189 eq4162
    | (have j0 := eq4162 X0 X1
       grind)
    | exact resolve eq4162 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162
  have eq5985 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4166 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4166
    | exact resolve eq4166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq6047 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5985 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5985
    | (have j0 := eq5985 X0 X1
       grind)
    | exact resolve eq5985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5985
  have eq6135 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq203 (σ X0) (σ X1)
       grind)
    | exact superpose eq203 eq15
    | (have j1 := eq203 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15859 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X1))) ∨ (k (σ X0) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq152 (σ X0) (σ X1)
       have i₂ := eq2123 X0 X1 X2
       grind)
    | exact superpose eq2123 eq152
    | (have j1 := eq2123 X0 (k X0 X1) X2
       grind)
    | exact resolve eq152 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq44170 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k (σ X1) X2) = X2 ∨ (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15859 X1 (M.op X0 X1) X2
       have i₂ := eq300 X1 X0
       grind)
    | exact superpose eq300 eq15859
    | (have j0 := eq15859 X1 (M.op X0 X1) X2
       grind)
    | exact resolve eq15859 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq15859
  have eq44645 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 X1))) ∨ (k (σ X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq44170 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44170
  have eq73913 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq44645 X2 X1 (σ X0)
       grind)
    | exact superpose eq44645 eq22
    | (have j1 := eq44645 X2 X1 X2
       grind)
    | exact resolve eq22 eq44645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq44645
  have eq74050 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X1) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73913 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq73913
    | (have j0 := eq73913 X0 X1 X2
       grind)
    | exact resolve eq73913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73913
  have eq74119 : ∀ X0 X1 X2 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X1) (σ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74050 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq74050
    | (have j0 := eq74050 X0 X1 X2
       grind)
    | exact resolve eq74050 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74050
  have eq76381 : ∀ X0 X1 X2 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq189 (σ (M.op X1 X0)) (σ X0)
       have i₂ := eq74119 X2 X0 X1
       grind)
    | exact superpose eq74119 eq189
    | (have j1 := eq74119 X2 X0 X2
       grind)
    | exact resolve eq189 eq74119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq74119
  have eq424823 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6135 x y
       grind)
    | exact superpose eq6135 eq16
    | (have j1 := eq6135 x y
       grind)
    | exact resolve eq16 eq6135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6135
  have eq439046 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq424823
       have i₂ := eq6047 y x
       grind)
    | exact superpose eq6047 eq424823
    | (have j1 := eq6047 (σ y) (σ x)
       grind)
    | (have r₁ := eq424823
       have r₂ := eq6047 y x
       grind)
    | exact resolve eq424823 eq6047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6047 eq424823
  have eq439047 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq439046
  have eq440361 : y = (k (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq787 y (σ x)
       have i₂ := eq439047
       grind)
    | exact superpose eq439047 eq787
    | exact resolve eq787 eq439047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq439047
  have eq440571 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq440361
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq440361
    | exact resolve eq440361 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440361
  have eq442074 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq203 x y
       have i₂ := eq440571
       grind)
    | exact superpose eq440571 eq203
    | (have j0 := eq203 x y
       grind)
    | exact resolve eq203 eq440571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440571
  have eq442165 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq442074
  have eq448542 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq152 x y
       have i₂ := eq442165
       grind)
    | exact superpose eq442165 eq152
    | exact resolve eq152 eq442165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442165
  have eq448732 : x = (M.op x y) := by grind
  clear eq448542
  have eq450402 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76381 y x x
       have i₂ := eq448732
       grind)
    | exact superpose eq448732 eq76381
    | (have j0 := eq76381 y x X0
       grind)
    | exact resolve eq76381 eq448732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76381
  have eq538358 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq450402 X0
       grind)
    | exact superpose eq450402 eq16
    | (have j1 := eq450402 X0
       grind)
    | exact resolve eq16 eq450402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450402
  have eq538653 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq538358 X0
       have i₂ := eq448732
       grind)
    | exact superpose eq448732 eq538358
    | (have j0 := eq538358 X0
       grind)
    | exact resolve eq538358 eq448732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448732 eq538358
  have eq538654 : ∀ X0 : G, (k y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq538653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538653
  have eq540154 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq203 y X0
       have i₂ := eq538654 X0
       grind)
    | exact superpose eq538654 eq203
    | (have j0 := eq203 y X0
       grind)
    | exact resolve eq203 eq538654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540228 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 y
       have i₂ := eq538654 (τ X0)
       grind)
    | exact superpose eq538654 eq18
    | exact resolve eq18 eq538654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq538654
  have eq540309 : ∀ X0 : G, (k (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq540228 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq540228
    | exact resolve eq540228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540228
  have eq541868 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq203 (σ y) X0
       have i₂ := eq540309 X0
       grind)
    | exact superpose eq540309 eq203
    | (have j0 := eq203 (σ y) X0
       grind)
    | exact resolve eq203 eq540309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq540309
  have eq559760 : ∀ X0 : G, y = (M.op y X0) ∨ y = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq152 y X0
       have i₂ := eq540154 X0
       grind)
    | exact superpose eq540154 eq152
    | (have j1 := eq540154 X0
       grind)
    | exact resolve eq152 eq540154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540154
  have eq560285 : ∀ X0 : G, y = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq559760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559760
  have eq562369 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq560285 (M.op X0 X0)
       grind)
    | exact superpose eq560285 eq24
    | exact resolve eq24 eq560285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560285
  have eq962018 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq152 (σ y) X0
       have i₂ := eq541868 X0
       grind)
    | exact superpose eq541868 eq152
    | (have j1 := eq541868 X0
       grind)
    | exact resolve eq152 eq541868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq541868
  have eq962193 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq962018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962018
  have eq965561 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 (σ y) X0
       have i₂ := eq962193 (M.op X0 X0)
       grind)
    | exact superpose eq962193 eq24
    | exact resolve eq24 eq962193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq962193
  have eq969712 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq965561 (σ x)
       grind)
    | exact superpose eq965561 eq16
    | exact resolve eq16 eq965561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965561
  have eq970002 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq969712
       have i₂ := eq562369 x
       grind)
    | exact superpose eq562369 eq969712
    | exact resolve eq969712 eq562369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562369 eq969712
  have eq970003 : False := by grind
  exact eq970003

/-- `Equation1037`: `x = x ◇ ((y ◇ (x ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then Y else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_y_x_pxy_Equation1037 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1037 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1037.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X0 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X0 X2
       have i₂ := eq9 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op x (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) x)
       have i₂ := eq9 (M.op X0 (M.op X1 X1)) x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq83 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X1) X1 x
       have i₂ := eq25 (M.op X1 X1) X1
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq83 X0 (M.op x (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq25 x (M.op X0 X0)
       grind)
    | exact superpose eq25 eq83
    | exact resolve eq83 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq123 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq52
    | (have j0 := eq52 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq52 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq52 (τ X0) X1
       grind)
    | exact superpose eq52 eq18
    | (have j1 := eq52 (τ X0) X1
       grind)
    | exact resolve eq18 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq133 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq25 X0 X0
       have i₂ := eq113 X0
       grind)
    | exact superpose eq113 eq25
    | exact resolve eq25 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq189 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 X0
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq25
    | exact resolve eq25 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq279 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X1 X0)
       have i₂ := eq189 X0 X1
       grind)
    | exact superpose eq189 eq12
    | (have j0 := eq12 X0 (M.op X1 X0)
       grind)
    | exact resolve eq12 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | (have r₁ := eq279 X0 X1
       have r₂ := eq133 X0
       grind)
    | exact resolve eq279 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq429 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (σ X0))) = (M.op (M.op X2 (M.op (σ X0) (σ X0))) (σ (k X0 X1))) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (σ X0) X2 (σ X1)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq24
    | (have j1 := eq39 X0 X1
       grind)
    | exact resolve eq24 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq39
  have eq451 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq429 X0 X1 X2
       have i₂ := eq133 (σ X0)
       grind)
    | exact superpose eq133 eq429
    | (have j0 := eq429 X0 X1 X2
       grind)
    | exact resolve eq429 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq475 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq451 X0 X1 X2
       have i₂ := eq133 (σ X0)
       grind)
    | exact superpose eq133 eq451
    | (have j0 := eq451 X0 X1 X2
       grind)
    | exact resolve eq451 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq901 : ∀ X0 X1 : G, (k (M.op X1 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq288 (M.op X1 X0) X0
       have i₂ := eq189 X0 X1
       grind)
    | exact superpose eq189 eq288
    | exact resolve eq288 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq288
  have eq1070 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 (M.op X1 (τ X0))
       have i₂ := eq901 (τ X0) X1
       grind)
    | exact superpose eq901 eq19
    | exact resolve eq19 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq901
  have eq1071 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1070
    | exact resolve eq1070 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq2866 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq125 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125
    | exact resolve eq125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq2925 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2866 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2866
    | (have j0 := eq2866 X0 X1
       grind)
    | exact resolve eq2866 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866
  have eq4534 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq123 x y
       grind)
    | exact superpose eq123 eq16
    | (have j1 := eq123 x y
       grind)
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq9996 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (σ (k (τ X0) X2))) ∨ (M.op X0 (σ X2)) = X0 ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq475 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq475
    | exact resolve eq475 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq10191 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (k X0 (σ X2))) ∨ (M.op X0 (σ X2)) = X0 ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9996 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq9996
    | (have j0 := eq9996 X0 X1 X2
       grind)
    | exact resolve eq9996 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9996
  have eq50182 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq4534
       have i₂ := eq2925 x y
       grind)
    | exact superpose eq2925 eq4534
    | (have j1 := eq2925 x y
       grind)
    | (have r₁ := eq4534
       have r₂ := eq2925 x y
       grind)
    | (have r₁ := eq4534
       have r₂ := eq2925 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4534
       have r₂ := eq2925 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4534 eq2925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2925 eq4534
  have eq50183 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by grind
  clear eq50182
  have eq53550 : ∀ X0 X1 : G, (M.op X0 (k X0 (σ X1))) = X0 ∨ (M.op X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10191 X0 X0 x
       have i₂ := eq133 X0
       grind)
    | exact superpose eq133 eq10191
    | (have j0 := eq10191 X0 X1 X1
       grind)
    | exact resolve eq10191 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10191
  have eq108947 : ∀ X0 X1 : G, (M.op X1 (k X1 X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53550 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53550
    | exact resolve eq53550 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109034 : ∀ X0 X1 : G, (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (σ X0) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53550 (σ (M.op X1 (τ (σ X0)))) X0
       have i₂ := eq1071 (σ X0) X1
       grind)
    | exact superpose eq1071 eq53550
    | (have j0 := eq53550 (σ (M.op X1 (τ (σ X0)))) X0
       grind)
    | exact resolve eq53550 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071 eq53550
  have eq109664 : ∀ X0 X1 : G, (σ (M.op X1 (τ (σ X0)))) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ X0)) ∨ (σ X0) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq109034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109034
  have eq109783 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq109664 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109664
    | (have j0 := eq109664 X0 X1
       grind)
    | exact resolve eq109664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109664
  have eq109828 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq109783 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109783
    | (have j0 := eq109783 X0 X1
       grind)
    | exact resolve eq109783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109783
  have eq339783 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq50183
       grind)
    | exact superpose eq50183 eq10
    | exact resolve eq10 eq50183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50183
  have eq339804 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq339783
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq339783
    | exact resolve eq339783 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339783
  have eq339805 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq128 x y
       grind)
    | (have r₁ := eq339804
       have r₂ := eq128 x y
       grind)
    | exact resolve eq339804 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq339804
  have eq340441 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq108947 y x
       have i₂ := eq339805
       grind)
    | exact superpose eq339805 eq108947
    | (have j0 := eq108947 y x
       grind)
    | exact resolve eq108947 eq339805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108947 eq339805
  have eq340490 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq340441
  have eq341377 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109828 y x
       have i₂ := eq340490
       grind)
    | exact superpose eq340490 eq109828
    | exact resolve eq109828 eq340490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109828
  have eq341409 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq341377
  have eq349646 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq341409
       grind)
    | exact superpose eq341409 eq16
    | exact resolve eq16 eq341409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341409
  have eq350548 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq349646
       have i₂ := eq340490
       grind)
    | exact superpose eq340490 eq349646
    | exact resolve eq349646 eq340490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340490 eq349646
  have eq350551 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq350548
  have eq350552 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq350551
  have eq351233 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq350552
       grind)
    | exact superpose eq350552 eq10
    | exact resolve eq10 eq350552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350552
  have eq351397 : x = y ∨ x = y := by
    first
    | (have i₁ := eq351233
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq351233
    | exact resolve eq351233 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351233
  have eq351398 : x = y := by grind
  clear eq351397
  have eq352089 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq351398
       grind)
    | exact superpose eq351398 eq16
    | exact resolve eq16 eq351398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351398
  have eq352090 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq352089
       have i₂ := eq133 x
       grind)
    | exact superpose eq133 eq352089
    | exact resolve eq352089 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352089
  have eq352091 : False := by grind
  exact eq352091

/-- `Equation1049`: `x = x ◇ ((y ◇ (y ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1049 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1049 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1049.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X1)) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq34 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq47 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X0) ≠ (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op (M.op X0 (M.op X0 X0)) X0)
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X1 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X1 X1)) X1)
       have r₂ := eq9 (M.op (M.op X1 (M.op X1 X1)) X1) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) (τ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X1) (τ X1)
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq75 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq97 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) ≠ X0 ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq48 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq12 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) ≠ X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq97 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq97 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq97 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq204 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq73 (τ X0) X2 X1
       grind)
    | exact superpose eq73 eq18
    | (have j1 := eq73 (τ X0) X2 X1
       grind)
    | exact resolve eq18 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq213 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq213 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq220 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq214 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq214 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq228 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq220 (σ X0)
       grind)
    | exact superpose eq220 eq15
    | exact resolve eq15 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0 X0
       have i₂ := eq220 (τ X0)
       grind)
    | exact superpose eq220 eq39
    | exact resolve eq39 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq230 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq230
    | exact resolve eq230 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq235 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq228 X0
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq228
    | exact resolve eq228 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq296 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq75 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | (have j1 := eq75 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq308 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq296 X0 X1 X2
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq296
    | (have j0 := eq296 X0 X1 X2
       grind)
    | exact resolve eq296 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq326 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq9
    | exact resolve eq9 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (τ X0) (τ (M.op X0 X0))) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq9
    | exact resolve eq9 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq326 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq326
    | exact resolve eq326 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq595 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (σ (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq235 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq235 eq540
    | exact resolve eq540 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq605 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq595
    | exact resolve eq595 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq607 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq235 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq235 eq605
    | exact resolve eq605 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq609 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq607 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq607
    | exact resolve eq607 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq1289 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (τ (M.op (M.op X0 (M.op X0 X0)) X0)) (τ (M.op (M.op X0 (M.op X0 X0)) X0))) (τ (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 (M.op (M.op X0 (M.op X0 X0)) X0) X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq432
    | exact resolve eq432 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1377 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0))) (τ (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1289 X0 X1
       have i₂ := eq233 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq233 eq1289
    | exact resolve eq1289 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1398 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (M.op X0 (M.op X0 X0)) X0)) (τ (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1377 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq1377
    | exact resolve eq1377 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1404 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1398 X0 X1
       have i₂ := eq233 (M.op (M.op X0 (M.op X0 X0)) X0)
       grind)
    | exact superpose eq233 eq1398
    | exact resolve eq1398 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398
  have eq1407 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 (M.op X0 X0)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1404 X0 X1
       have i₂ := eq9 (M.op (M.op X0 (M.op X0 X0)) X0) X0
       grind)
    | exact superpose eq9 eq1404
    | exact resolve eq1404 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq6091 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 X0 X1
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq6320 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6091 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq6091
    | (have j0 := eq6091 X0 X0
       grind)
    | exact resolve eq6091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6091
  have eq11509 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op (M.op X1 (M.op X1 X1)) X1))) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) ∨ (τ X0) = (k (τ X0) (M.op (M.op X1 (M.op X1 X1)) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 X0 (τ X0) X2
       have i₂ := eq48 X0 (τ X0)
       grind)
    | exact superpose eq48 eq204
    | (have j0 := eq204 X0 (τ X0) X2
       have j1 := eq48 X0 (τ X0)
       grind)
    | exact resolve eq204 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq11759 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op (M.op X1 (M.op X1 X1)) X1))) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11509 X0 X1 X2
       have j1 := eq111 (τ X0) X1 X2
       grind)
    | (have r₁ := eq11509 X0 X1 X2
       have r₂ := eq111 (τ X0) X1 X2
       grind)
    | exact resolve eq11509 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq11509
  have eq11780 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op (M.op X1 (M.op X1 X1)) X1))) = (k (σ (τ X0)) X0) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq11759 X0 X1 X2
       have j1 := eq12 (τ X0) X2
       grind)
    | (have r₁ := eq11759 X0 X1 X2
       have r₂ := eq12 (τ X0) X1
       grind)
    | exact resolve eq11759 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11759
  have eq11794 : ∀ X0 X1 X2 : G, (k X0 X0) = (σ (k (τ X0) (M.op (M.op X1 (M.op X1 X1)) X1))) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11780 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11780
    | (have j0 := eq11780 X0 X1 X2
       grind)
    | exact resolve eq11780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11780
  have eq11799 : ∀ X0 X1 X2 : G, (k X0 X0) = (k X0 (σ (M.op (M.op X1 (M.op X1 X1)) X1))) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11794 X0 X1 X2
       have i₂ := eq17 X0 (M.op (M.op X1 (M.op X1 X1)) X1)
       grind)
    | exact superpose eq17 eq11794
    | (have j0 := eq11794 X0 X1 X2
       grind)
    | exact resolve eq11794 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq11794
  have eq11802 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op X1 (M.op X1 X1)) X1))) ∨ (M.op (τ X0) X2) = (k (τ X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11799 X0 X1 X2
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq11799
    | (have j0 := eq11799 X0 X1 X2
       grind)
    | exact resolve eq11799 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq11799
  have eq23441 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq308 X0 X1 X2
       grind)
    | exact superpose eq308 eq10
    | (have j1 := eq308 X0 X1 X2
       grind)
    | exact resolve eq10 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq23775 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) X2) = (M.op (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23441 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23441
    | (have j0 := eq23441 X0 X1 X2
       grind)
    | exact resolve eq23441 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23441
  have eq36206 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq6320 X0 X2
       grind)
    | exact superpose eq6320 eq327
    | (have j0 := eq327 X0 X1
       have j1 := eq6320 X0 X2
       grind)
    | exact resolve eq327 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320
  have eq36348 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq36206 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36206
  have eq192943 : ∀ X0 X1 X2 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ (M.op (M.op X1 (M.op X1 X1)) X1)))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (σ (M.op (M.op X1 (M.op X1 X1)) X1))
       have i₂ := eq11802 (σ X0) X1 X2
       grind)
    | exact superpose eq11802 eq34
    | (have j1 := eq11802 (σ X0) X1 X2
       grind)
    | exact resolve eq34 eq11802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11802
  have eq192951 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192943 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X1 (M.op X1 X1)) X1)
       grind)
    | exact superpose eq10 eq192943
    | (have j0 := eq192943 X0 X1 X2
       grind)
    | exact resolve eq192943 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192943
  have eq192960 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) = (τ (σ (M.op X0 X0))) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192951 X0 X1 X2
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq192951
    | (have j0 := eq192951 X0 X1 X2
       grind)
    | exact resolve eq192951 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192951
  have eq192968 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) ∨ (M.op (τ (σ X0)) X2) = (k (τ (σ X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192960 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq192960
    | (have j0 := eq192960 X0 X1 X2
       grind)
    | exact resolve eq192960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192960
  have eq192969 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq192968 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq192968
    | (have j0 := eq192968 X0 X1 X2
       grind)
    | exact resolve eq192968 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192968
  have eq193033 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X1)) X1)) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq192969 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192969
  have eq193035 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193033 X0 X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq193033
    | (have j0 := eq193033 X0 X1
       grind)
    | exact resolve eq193033 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193033
  have eq193044 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op (M.op X1 (M.op X1 X1)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq193035 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq193035 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq193035 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq193035
  have eq193427 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 (M.op X1 X1)) X1))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op (M.op X1 (M.op X1 X1)) X1)
       have i₂ := eq193044 (σ X0) X1
       grind)
    | exact superpose eq193044 eq34
    | exact resolve eq34 eq193044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193044
  have eq193461 : ∀ X0 X1 : G, (k X0 (τ (M.op (M.op X1 (M.op X1 X1)) X1))) = (τ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq193427 X0 X1
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq193427
    | exact resolve eq193427 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193427
  have eq193522 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (M.op (M.op X1 (M.op X1 X1)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq193461 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq193461
    | exact resolve eq193461 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193461
  have eq194325 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ X0) (τ (M.op (M.op X1 (M.op X1 X1)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0
       have i₂ := eq193522 (σ X0) X1
       grind)
    | exact superpose eq193522 eq235
    | exact resolve eq235 eq193522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194359 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (τ (M.op (M.op X1 (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (τ (M.op (M.op X1 (M.op X1 X1)) X1))
       have i₂ := eq193522 (σ X0) X1
       grind)
    | exact superpose eq193522 eq34
    | exact resolve eq34 eq193522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq193522
  have eq194401 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k X0 (τ (τ (M.op (M.op X1 (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq194359 X0 X1
       have i₂ := eq235 X0
       grind)
    | exact superpose eq235 eq194359
    | exact resolve eq194359 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194359
  have eq194480 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (τ (M.op (M.op X1 (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq194401 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq194401
    | exact resolve eq194401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194401
  have eq195950 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ (τ (M.op (M.op X1 (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0
       have i₂ := eq194480 (τ X0) X1
       grind)
    | exact superpose eq194480 eq233
    | exact resolve eq233 eq194480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq194480
  have eq195995 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 (τ (M.op (M.op X1 (M.op X1 X1)) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq195950 X0 X1
       have i₂ := eq39 (τ (M.op (M.op X1 (M.op X1 X1)) X1)) X0
       grind)
    | exact superpose eq39 eq195950
    | exact resolve eq195950 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq195950
  have eq197930 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq23775 x y X0
       grind)
    | exact superpose eq23775 eq16
    | (have j1 := eq23775 x y X0
       grind)
    | exact resolve eq16 eq23775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23775
  have eq197936 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq197930 X0
       have j1 := eq36348 y X0 x
       grind)
    | (have r₁ := eq197930 X0
       have r₂ := eq36348 y x x
       grind)
    | exact resolve eq197930 eq36348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36348 eq197930
  have eq197970 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ y) (τ (M.op (M.op X0 (M.op X0 X0)) X0))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq194325 y X0
       have i₂ := eq197936 (τ (M.op (M.op X0 (M.op X0 X0)) X0))
       grind)
    | exact superpose eq197936 eq194325
    | exact resolve eq194325 eq197936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194325
  have eq198006 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (τ (M.op (σ y) (τ (M.op (M.op X0 (M.op X0 X0)) X0)))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq195995 (σ y) X0
       have i₂ := eq197936 (τ (M.op (M.op X0 (M.op X0 X0)) X0))
       grind)
    | exact superpose eq197936 eq195995
    | exact resolve eq195995 eq197936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195995 eq197936
  have eq198023 : (τ (M.op (σ y) (σ y))) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198006 x
       have i₂ := eq1407 x (σ y)
       grind)
    | exact superpose eq1407 eq198006
    | exact resolve eq198006 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198006
  have eq198043 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq197970 x
       have i₂ := eq1407 x (σ y)
       grind)
    | exact superpose eq1407 eq197970
    | exact resolve eq197970 eq1407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407 eq197970
  have eq198063 : y = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198023
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq198023
    | exact resolve eq198023 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198023
  have eq198086 : y = (τ (σ (M.op y y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198063
       have i₂ := eq235 y
       grind)
    | exact superpose eq235 eq198063
    | exact resolve eq198063 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq198063
  have eq198090 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198086
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq198086
    | exact resolve eq198086 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198086
  have eq198130 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq198090
       grind)
    | exact superpose eq198090 eq9
    | exact resolve eq9 eq198090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199001 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq198130 X0
       have i₂ := eq198090
       grind)
    | exact superpose eq198090 eq198130
    | exact resolve eq198130 eq198090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198130
  have eq199008 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq199001 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199001
  have eq199021 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq199008 X0
       have i₂ := eq198090
       grind)
    | exact superpose eq198090 eq199008
    | exact resolve eq199008 eq198090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198090
  have eq199034 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq609 y X0
       have i₂ := eq199008 y
       grind)
    | exact superpose eq199008 eq609
    | exact resolve eq609 eq199008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq199008
  have eq199214 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq199021 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199021
  have eq200549 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq199034 X0
       have i₂ := eq198043
       grind)
    | exact superpose eq198043 eq199034
    | exact resolve eq199034 eq198043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198043 eq199034
  have eq200606 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq200549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200549
  have eq200900 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200606 (σ x)
       grind)
    | exact superpose eq200606 eq16
    | exact resolve eq16 eq200606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200606
  have eq201160 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq200900
       have i₂ := eq199214 x
       grind)
    | exact superpose eq199214 eq200900
    | exact resolve eq200900 eq199214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199214 eq200900
  have eq201161 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq201160
  have eq201162 : x = (M.op x x) := by grind
  clear eq201161
  have eq201164 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq201162
       grind)
    | exact superpose eq201162 eq12
    | (have j0 := eq12 x X0
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq201162
       grind)
    | exact resolve eq12 eq201162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201188 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq327 x X0
       have i₂ := eq201162
       grind)
    | exact superpose eq201162 eq327
    | (have j0 := eq327 x X0
       grind)
    | exact resolve eq327 eq201162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq201162
  have eq201368 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq201188 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201188
  have eq201370 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq201164 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201164
  have eq217352 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq201368 (σ X0)
       grind)
    | exact superpose eq201368 eq15
    | exact resolve eq15 eq201368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201368
  have eq217499 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq217352 X0
       have i₂ := eq201370 X0
       grind)
    | exact superpose eq201370 eq217352
    | exact resolve eq217352 eq201370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201370 eq217352
  have eq234018 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217499 y
       grind)
    | exact superpose eq217499 eq16
    | (have r₁ := eq16
       have r₂ := eq217499 y
       grind)
    | exact resolve eq16 eq217499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217499
  have eq234248 : False := by grind
  exact eq234248

/-- `Equation1053`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_x_pyx_Equation1053 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1053 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1053.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X1 X2)) X2)
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2))) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq25 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq12
    | (have r₁ := eq12 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq26 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq36 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq36
    | (have j0 := eq36 X0 X1
       grind)
    | (have r₁ := eq36 X0 (M.op X0 X0)
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq36 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq39 (σ X0)
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq47
    | exact resolve eq47 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq47
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | (have i₁ := eq55 X0 X1
       have i₂ := eq26 X0 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq26 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 (k (M.op X0 X0) X1)
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | (have r₁ := eq57 X0 (M.op X0 X0)
       have r₂ := eq42 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq42 X0 (k (M.op X0 X0) X1)
       grind)
    | exact resolve eq57 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq57
  have eq71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq71
    | (have j0 := eq71 X0 X1
       grind)
    | exact resolve eq71 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq160 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq26
    | exact resolve eq26 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq86
    | (have j0 := eq86 (σ X0) X1
       grind)
    | exact resolve eq86 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq211 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq202 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq202 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq202 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq218 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq172 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq172
    | (have j0 := eq172 X0 X1
       grind)
    | exact resolve eq172 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq223 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq218 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq218
    | (have j0 := eq218 X0 X1
       grind)
    | exact resolve eq218 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq218
  have eq714 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq718 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq714 X0 X1
       have j1 := eq223 X1 X0
       grind)
    | (have r₁ := eq714 X1 X0
       have r₂ := eq223 X0 X1
       grind)
    | exact resolve eq714 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq714
  have eq854 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq211 X1 (τ X0)
       grind)
    | exact superpose eq211 eq18
    | (have j1 := eq211 X1 X1
       grind)
    | exact resolve eq18 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq865 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq211 X0 X2
       grind)
    | exact superpose eq211 eq160
    | (have j1 := eq211 X0 X2
       grind)
    | exact resolve eq160 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq211
  have eq1743 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq718 X1 X0
       grind)
    | exact superpose eq718 eq10
    | (have j1 := eq718 X1 X0
       grind)
    | exact resolve eq10 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1777 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1743 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1743
    | (have j0 := eq1743 X0 X1
       grind)
    | exact resolve eq1743 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq3788 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq865 y (σ x) X0
       grind)
    | exact superpose eq865 eq16
    | (have j1 := eq865 y x X0
       grind)
    | exact resolve eq16 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq17127 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq854 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq854
    | (have j0 := eq854 X0 X1
       grind)
    | exact resolve eq854 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq17423 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17127 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17127
    | (have j0 := eq17127 X0 X1
       grind)
    | exact resolve eq17127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17127
  have eq17856 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1777 y x
       grind)
    | exact superpose eq1777 eq16
    | (have j1 := eq1777 y x
       grind)
    | exact resolve eq16 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq18001 : y = (M.op y y) := by
    first
    | (have j1 := eq17423 x y
       grind)
    | (have r₁ := eq17856
       have r₂ := eq17423 x y
       grind)
    | exact resolve eq17856 eq17423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17423 eq17856
  have eq18078 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 y X0
       have i₂ := eq18001
       grind)
    | exact superpose eq18001 eq26
    | exact resolve eq26 eq18001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq18080 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq59 y x
       have i₂ := eq18001
       grind)
    | exact superpose eq18001 eq59
    | exact resolve eq59 eq18001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq18001
  have eq18561 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq3788 X0
       have i₂ := eq18078 x
       grind)
    | exact superpose eq18078 eq3788
    | (have j0 := eq3788 X0
       grind)
    | exact resolve eq3788 eq18078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788
  have eq18562 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq18561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18561
  have eq18564 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq18562 X0
       have i₂ := eq18080 X0
       grind)
    | exact superpose eq18080 eq18562
    | exact resolve eq18562 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18080 eq18562
  have eq19047 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq18078 X0
       have i₂ := eq18564 X0
       grind)
    | exact superpose eq18564 eq18078
    | exact resolve eq18078 eq18564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18078 eq18564
  have eq19710 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19047 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq19047 eq16
    | exact resolve eq16 eq19047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20165 : False := by grind
  exact eq20165

/-- `Equation1053`: `x = x ◇ ((y ◇ (y ◇ z)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_x_pxx_pyx_Equation1053 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1053 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1053.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X1 X2)) X2)
       have i₂ := eq9 (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2))) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq21 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq73 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (M.op X0 X0)
       have i₂ := eq32 X0 (τ X1)
       grind)
    | exact superpose eq32 eq18
    | exact resolve eq18 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 (M.op X0 X0) X1
       have i₂ := eq32 X0 (σ X1)
       grind)
    | exact superpose eq32 eq73
    | exact resolve eq73 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | (have j1 := eq37 (σ X0)
       grind)
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (σ (M.op X0 X0))
       have i₂ := eq75 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq75 eq37
    | (have j0 := eq37 (σ (M.op X0 X0))
       grind)
    | exact resolve eq37 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq75
  have eq173 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq222 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq234 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq222 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq222 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq222 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq222 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq348 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq234 X1 (τ X0)
       grind)
    | exact superpose eq234 eq18
    | (have j1 := eq234 X1 X1
       grind)
    | exact resolve eq18 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq234 X0 X2
       grind)
    | exact superpose eq234 eq24
    | (have j1 := eq234 X0 X2
       grind)
    | exact resolve eq24 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq234 X0 X1
       grind)
    | exact superpose eq234 eq88
    | (have j1 := eq234 X0 X2
       grind)
    | exact resolve eq88 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq234
  have eq1047 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ (M.op X0 X0)) X1
       have i₂ := eq173 X0
       grind)
    | exact superpose eq173 eq24
    | exact resolve eq24 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq1130 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq358 X0 X0 X2
       grind)
    | exact superpose eq358 eq1047
    | (have j1 := eq358 (σ X0) X1 X2
       grind)
    | exact resolve eq1047 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq1047
  have eq1421 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq1983 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1130 y (σ x) X0
       grind)
    | exact superpose eq1130 eq16
    | (have j1 := eq1130 y x X0
       grind)
    | exact resolve eq16 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq6765 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq361 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq361 eq15
    | (have j1 := eq361 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq6805 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6765 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6765
    | (have j0 := eq6765 X0 X1 X2
       grind)
    | exact resolve eq6765 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6765
  have eq11704 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq348 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq11922 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11704 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq11704
    | (have j0 := eq11704 X0 X1
       grind)
    | exact resolve eq11704 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11704
  have eq12040 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 X1
       have i₂ := eq11922 X0 X1
       grind)
    | exact superpose eq11922 eq32
    | (have j1 := eq11922 X2 X0
       grind)
    | exact resolve eq32 eq11922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq11922
  have eq12136 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1421 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1421
    | (have j0 := eq1421 (τ X0)
       grind)
    | exact resolve eq1421 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1421
  have eq12158 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12136 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12136
    | (have j0 := eq12136 X0
       grind)
    | exact resolve eq12136 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12136
  have eq12167 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12158 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12158
    | (have j0 := eq12158 X0
       grind)
    | exact resolve eq12158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12158
  have eq59764 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq6805 x y X0
       grind)
    | exact superpose eq6805 eq16
    | (have j1 := eq6805 X0 y X0
       grind)
    | exact resolve eq16 eq6805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6805
  have eq59989 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq59764 X0
       have j1 := eq12040 y X0 x
       grind)
    | (have r₁ := eq59764 X0
       have r₂ := eq12040 y x x
       grind)
    | exact resolve eq59764 eq12040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12040 eq59764
  have eq61251 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12167 y
       have i₂ := eq59989 y
       grind)
    | exact superpose eq59989 eq12167
    | (have j0 := eq12167 y
       grind)
    | (have r₁ := eq12167 y
       have r₂ := eq59989 y
       grind)
    | exact resolve eq12167 eq59989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12167
  have eq61377 : y = (M.op y y) := by grind
  clear eq61251
  have eq62521 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq61377
       grind)
    | exact superpose eq61377 eq24
    | exact resolve eq24 eq61377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq61377
  have eq63658 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1983 X0
       have i₂ := eq62521 x
       grind)
    | exact superpose eq62521 eq1983
    | (have j0 := eq1983 X0
       grind)
    | exact resolve eq1983 eq62521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq63659 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq63658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63658
  have eq63663 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq63659 X0
       have i₂ := eq59989 X0
       grind)
    | exact superpose eq59989 eq63659
    | exact resolve eq63659 eq59989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59989 eq63659
  have eq64683 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq62521 X0
       have i₂ := eq63663 X0
       grind)
    | exact superpose eq63663 eq62521
    | exact resolve eq62521 eq63663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62521 eq63663
  have eq66287 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64683 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq64683 eq16
    | exact resolve eq16 eq64683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67328 : False := by grind
  exact eq67328
