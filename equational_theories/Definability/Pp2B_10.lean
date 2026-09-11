import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq354 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq78 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq78 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq381 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq382 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq382
    | (have j0 := eq382 X0 X1
       grind)
    | exact resolve eq382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq387 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       have j1 := eq378 X1 X0
       grind)
    | (have r₁ := eq384 X1 X0
       have r₂ := eq378 X0 X1
       grind)
    | (have r₁ := eq384 X1 (k X0 X1)
       have r₂ := eq378 X0 X1
       grind)
    | (have r₁ := eq384 X1 X1
       have r₂ := eq378 X1 X1
       grind)
    | exact resolve eq384 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq384
  have eq835 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq387 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq387 y x
       grind)
    | exact superpose eq387 eq16
    | (have j1 := eq387 y x
       grind)
    | exact resolve eq16 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq870 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq835 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq835
    | (have j0 := eq835 X0 X1
       grind)
    | exact resolve eq835 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq835
  have eq872 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq870
    | exact resolve eq870 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq931 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq872 (τ X0) X1
       grind)
    | exact superpose eq872 eq18
    | (have j1 := eq872 (τ X0) X1
       grind)
    | exact resolve eq18 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq872
  have eq2499 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq931 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq931
    | exact resolve eq931 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq2561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2499 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2499
    | (have j0 := eq2499 X0 X1
       grind)
    | exact resolve eq2499 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2636 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq843
       have i₂ := eq2561 x y
       grind)
    | exact superpose eq2561 eq843
    | (have j1 := eq2561 (σ x) (σ y)
       grind)
    | (have r₁ := eq843
       have r₂ := eq2561 x y
       grind)
    | exact resolve eq843 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2637 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2636
  have eq2686 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2637
  have eq2729 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq843
       have i₂ := eq2686
       grind)
    | exact superpose eq2686 eq843
    | exact resolve eq843 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq2686
  have eq2730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2729
  have eq2731 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2730
  have eq2859 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq2731
  have eq2904 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq2859
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2859
    | exact resolve eq2859 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2859
  have eq3143 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2904
       grind)
    | exact superpose eq2904 eq16
    | exact resolve eq16 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq3285 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3143
       have i₂ := eq2561 x y
       grind)
    | exact superpose eq2561 eq3143
    | (have j1 := eq2561 x y
       grind)
    | (have r₁ := eq3143
       have r₂ := eq2561 x y
       grind)
    | exact resolve eq3143 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq3286 : x = (M.op y y) := by grind
  clear eq3285
  have eq3292 : (M.op x y) = (k x y) := by grind
  clear eq3286
  have eq3423 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq3143
       have i₂ := eq3292
       grind)
    | exact superpose eq3292 eq3143
    | exact resolve eq3143 eq3292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143 eq3292
  have eq3426 : False := by grind
  exact eq3426

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation2046 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X0 X0) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq21 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 X2
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq81 X1 X1
       have i₂ := eq81 X1 X1
       grind)
    | exact superpose eq81 eq81
    | exact resolve eq81 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq81 X1 X1
       grind)
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X0 (M.op X0 X1)
       have i₂ := eq81 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq21 X0 X1 (M.op X1 X0)
       have i₂ := eq81 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq81 eq21
    | exact resolve eq21 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq273 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ X2) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq72
    | exact resolve eq72 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X1) x
       have i₂ := eq72 X1 X1
       grind)
    | exact superpose eq72 eq20
    | (have j1 := eq72 X0 X0
       grind)
    | exact resolve eq20 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq279 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq72 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq72 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | exact resolve eq12 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq72 X0 X0
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X0 X0
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (M.op (M.op (σ X1) (σ X1)) X2) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq9
    | (have j1 := eq72 X1 X1
       grind)
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq294 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) X1) (M.op X2 (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq280 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq295 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq296 : ∀ X0 X1 : G, (σ (k X0 X0)) = (M.op (σ X0) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq301 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq295 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq295 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq295 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq611 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X0 X2 X0
       have i₂ := eq89 X0 X2 X1
       grind)
    | (have i₁ := eq93 X0 X2 X0
       have i₂ := eq89 X0 X1 X2
       grind)
    | exact superpose eq89 eq93
    | exact resolve eq93 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (M.op X0 X0) X1 (M.op x X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq93
    | exact resolve eq93 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k (τ X0) (τ X0))) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq294 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq294
    | exact resolve eq294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq696 : ∀ X0 X1 X2 : G, (M.op (M.op (k (σ (τ X0)) X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq656 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq656
    | (have j0 := eq656 X0 X1 X2
       grind)
    | exact resolve eq656 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq700 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq696 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq696
    | (have j0 := eq696 X0 X1 X2
       grind)
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq813 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = (M.op (σ (τ X0)) (M.op X1 (k (σ (τ X0)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq296 (τ X0) X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq296
    | (have j0 := eq296 (τ X0) X1
       grind)
    | exact resolve eq296 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq838 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op X1 (k X0 X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq813 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq813
    | (have j0 := eq813 X0 X1
       grind)
    | exact resolve eq813 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq844 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op X1 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq838
    | (have j0 := eq838 X0 X1
       grind)
    | exact resolve eq838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq864 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 (M.op X0 X1) (M.op (M.op X0 X0) X0)
       have i₂ := eq19 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq19 eq615
    | exact resolve eq615 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq907 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq864 X0 X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq864
    | exact resolve eq864 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq986 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq290 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq290
    | (have j0 := eq290 (τ X0) (τ X1)
       grind)
    | exact resolve eq290 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq993 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq986 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq986
    | (have j0 := eq986 X0 X1
       grind)
    | exact resolve eq986 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq996 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq993 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq993
    | (have j0 := eq993 X0 X1
       grind)
    | exact resolve eq993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq997 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq996 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq996
    | (have j0 := eq996 X0 X1
       grind)
    | exact resolve eq996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq998 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq997
    | (have j0 := eq997 X0 X1
       grind)
    | exact resolve eq997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq999 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq998
    | (have j0 := eq998 X0 X1
       grind)
    | exact resolve eq998 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1142 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq907 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X0) X0)
       have i₂ := eq907 X0 X1
       grind)
    | exact superpose eq907 eq907
    | exact resolve eq907 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1164 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X0 X0) X0) X2
       have i₂ := eq907 X0 X1
       grind)
    | exact superpose eq907 eq9
    | exact resolve eq9 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1191 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1142 X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq1142
    | exact resolve eq1142 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1676 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X1 X0 X2
       have i₂ := eq1191 X0 X1
       grind)
    | (have i₁ := eq21 X1 X1 X2
       have i₂ := eq1191 X1 X1
       grind)
    | exact superpose eq1191 eq21
    | exact resolve eq21 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1191
  have eq2061 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op X0 (M.op (k X0 X0) X1)) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq93 (k X0 X0) X1 (M.op x X0)
       have i₂ := eq700 X0 X1 x
       grind)
    | exact superpose eq700 eq93
    | (have j1 := eq700 X0 X1 x
       grind)
    | exact resolve eq93 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq2261 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op (σ X0) (σ X0)) X1) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq2262 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op (M.op (σ X0) (σ X0)) X1) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq2261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq4477 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (k X1 (τ X2))
       have i₂ := eq273 X1 X2 (τ X0)
       grind)
    | exact superpose eq273 eq17
    | (have j1 := eq273 X1 X2 (τ X0)
       grind)
    | exact resolve eq17 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq273
  have eq4506 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4477 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4477
    | (have j0 := eq4477 X0 X1 X2
       grind)
    | exact resolve eq4477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4515 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (k (σ X1) X2) = (M.op (k (σ X1) X2) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4506 X0 X1 X2
       have i₂ := eq18 X2 X1
       grind)
    | exact superpose eq18 eq4506
    | (have j0 := eq4506 X0 X1 X2
       grind)
    | exact resolve eq4506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506
  have eq4521 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4515 X0 X1 X2
       have j1 := eq12 X0 (k (σ X1) X2)
       grind)
    | (have r₁ := eq4515 X0 X1 X2
       have r₂ := eq12 X0 (k (σ X1) X2)
       grind)
    | exact resolve eq4515 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515
  have eq4527 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (M.op X0 (k (σ X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4521 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4521
    | (have j0 := eq4521 X0 X1 X2
       grind)
    | exact resolve eq4521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4521
  have eq11538 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (M.op X1 (k X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4527 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4527
    | exact resolve eq4527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4527
  have eq12727 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq999 (M.op X0 X0) X0
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq999
    | (have j0 := eq999 (M.op X0 X0) X0
       have j1 := eq96 X0 X1
       grind)
    | (have r₁ := eq999 (M.op X0 X0) X0
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq999 (M.op X0 X0) X0
       have r₂ := eq96 X0 X0
       grind)
    | exact resolve eq999 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq999
  have eq12767 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq12727 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12727
  have eq12768 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) ≠ (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq12767 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12767
  have eq14173 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X0) X1) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2262 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2262
    | exact resolve eq2262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq14279 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14173 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq14173
    | (have j0 := eq14173 X0 X1
       grind)
    | exact resolve eq14173 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq14280 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14279 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq14279
    | (have j0 := eq14279 X0 X1
       grind)
    | exact resolve eq14279 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14279
  have eq14368 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq844 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq14280 X0 x
       grind)
    | exact superpose eq14280 eq844
    | (have j0 := eq844 X0 x
       have j1 := eq14280 X0 x
       grind)
    | exact resolve eq844 eq14280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq14280
  have eq14421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14368
  have eq14445 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14421 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq14421 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq14421 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14421
  have eq14466 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq14445 X0
       grind)
    | exact superpose eq14445 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq14482 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0 X0
       have i₂ := eq14445 X0
       grind)
    | exact superpose eq14445 eq290
    | (have j0 := eq290 X0 X0
       grind)
    | exact resolve eq290 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq14515 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq14445 (σ X0)
       grind)
    | exact superpose eq14445 eq15
    | exact resolve eq15 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14523 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq14445 (τ X0)
       grind)
    | exact superpose eq14445 eq35
    | exact resolve eq35 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14551 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq14482 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14482
  have eq14576 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14523 X0
       have i₂ := eq14445 X0
       grind)
    | exact superpose eq14445 eq14523
    | exact resolve eq14523 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14523
  have eq14582 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14515 X0
       have i₂ := eq14445 X0
       grind)
    | exact superpose eq14445 eq14515
    | exact resolve eq14515 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14515
  have eq14971 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X1) (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq14576 X0
       grind)
    | exact superpose eq14576 eq9
    | exact resolve eq9 eq14576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15010 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq14576 X0
       grind)
    | exact superpose eq14576 eq9
    | exact resolve eq9 eq14576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15044 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1164 (τ X0) (τ X0) x
       have i₂ := eq14576 X0
       grind)
    | exact superpose eq14576 eq1164
    | exact resolve eq1164 eq14576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14576
  have eq15163 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (M.op X2 (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq14582 X0
       grind)
    | exact superpose eq14582 eq9
    | exact resolve eq9 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15193 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op (M.op (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1676 (σ X0) X1 X2
       have i₂ := eq14582 X0
       grind)
    | exact superpose eq14582 eq1676
    | exact resolve eq1676 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15202 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq14582 X0
       grind)
    | exact superpose eq14582 eq9
    | exact resolve eq9 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16017 : ∀ X0 X1 X2 : G, (M.op (M.op (τ X0) X2) (τ X0)) = (τ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15010 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq92 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq92 eq15010
    | exact resolve eq15010 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16925 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15010 (M.op (σ (M.op X0 X0)) (σ X0)) X1
       have i₂ := eq15163 X0 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact superpose eq15163 eq15010
    | exact resolve eq15010 eq15163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15010
  have eq16926 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq15044 (M.op (σ (M.op X0 X0)) (σ X0)) X1
       have i₂ := eq15163 X0 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact superpose eq15163 eq15044
    | exact resolve eq15044 eq15163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15044 eq15163
  have eq17002 : ∀ X0 X1 : G, (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16926 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16926
    | exact resolve eq16926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16926
  have eq17003 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16925 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16925
    | exact resolve eq16925 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16925
  have eq17255 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) X1) (σ (τ X0))) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15202 (M.op (τ (M.op X0 X0)) (τ X0)) X1
       have i₂ := eq14971 X0 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact superpose eq14971 eq15202
    | exact resolve eq15202 eq14971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14971
  have eq17256 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15202 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq92 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq92 eq15202
    | exact resolve eq15202 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17429 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq17255 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17255
    | exact resolve eq17255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17255
  have eq17891 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (τ (M.op (M.op (σ X0) X2) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16017 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16017
    | exact resolve eq16017 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17903 : ∀ X0 X1 X3 : G, (τ (M.op (M.op X0 X1) X0)) = (τ (M.op (M.op X0 X3) X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16017 X0 X3 x
       have i₂ := eq16017 X0 X1 x
       grind)
    | exact superpose eq16017 eq16017
    | exact resolve eq16017 eq16017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17989 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (M.op (σ (M.op X0 X0)) X1)) X2) (τ (M.op (σ (M.op X0 X0)) X1))) = (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16017 (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0)) X2
       have i₂ := eq15202 X0 X1
       grind)
    | exact superpose eq15202 eq16017
    | exact resolve eq16017 eq15202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16017
  have eq18648 : ∀ X0 X1 X2 X3 : G, (τ (k (M.op (M.op X0 X2) X0) X3)) = (k (τ (M.op (M.op X0 X1) X0)) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq35 X3 (M.op (M.op X0 X2) X0)
       have i₂ := eq17903 X0 X2 X1
       grind)
    | (have i₁ := eq35 X3 (M.op (M.op X0 X2) X0)
       have i₂ := eq17903 X0 X1 X2
       grind)
    | exact superpose eq17903 eq35
    | exact resolve eq35 eq17903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17903
  have eq18759 : ∀ X0 X1 X2 X3 : G, (τ (k (M.op (M.op X0 X2) X0) X3)) = (τ (k (M.op (M.op X0 X1) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18648 X0 X1 X2 X3
       have i₂ := eq35 X3 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq35 eq18648
    | exact resolve eq18648 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18648
  have eq19665 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1) (τ (M.op (σ (M.op X0 X0)) (σ X0)))) = (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1 (M.op x X0)
       have i₂ := eq17002 X0 x
       grind)
    | exact superpose eq17002 eq89
    | exact resolve eq89 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq19683 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (τ (M.op (σ (M.op X0 X0)) (σ X0))) X2) (τ (M.op (σ (M.op X0 X0)) (σ X0)))) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq611 (τ (M.op (σ (M.op X0 X0)) (σ X0))) X1 (M.op X1 X0)
       have i₂ := eq17002 X0 X1
       grind)
    | exact superpose eq17002 eq611
    | exact resolve eq611 eq17002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17002
  have eq19736 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19683 X0 X1 x
       have i₂ := eq17989 X0 (σ X0) x
       grind)
    | exact superpose eq17989 eq19683
    | exact resolve eq19683 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19683
  have eq19745 : ∀ X0 : G, (τ (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = (M.op X0 (τ (M.op (σ (M.op X0 X0)) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq19665 X0 x
       have i₂ := eq17989 X0 (σ X0) x
       grind)
    | exact superpose eq17989 eq19665
    | exact resolve eq19665 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17989 eq19665
  have eq20172 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (τ (M.op (σ (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))) (σ (M.op (M.op X0 X1) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 X1 (M.op (M.op X0 X1) X0)
       have i₂ := eq17003 (M.op (M.op X0 X1) X0) (M.op X0 (M.op (M.op X0 X1) X0))
       grind)
    | exact superpose eq17003 eq611
    | exact resolve eq611 eq17003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17003
  have eq20392 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) X0)) = (τ (M.op (σ X0) (σ (M.op (M.op X0 X1) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq20172 X0 X1
       have i₂ := eq92 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq92 eq20172
    | exact resolve eq20172 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20172
  have eq20852 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (M.op (σ (M.op (M.op X0 X1) X0)) (M.op (σ X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (σ X0) X2 (σ X0)
       have i₂ := eq17256 X0 X1 X2
       grind)
    | exact superpose eq17256 eq93
    | exact resolve eq93 eq17256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq17256
  have eq22155 : ∀ X0 X1 X2 : G, (σ (k (M.op (τ (M.op X0 X0)) (τ X0)) X2)) = (k (M.op (M.op X0 X1) X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (M.op (τ (M.op X0 X0)) (τ X0)) X2
       have i₂ := eq17429 X0 X1
       grind)
    | exact superpose eq17429 eq15
    | exact resolve eq15 eq17429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17429
  have eq94327 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X3) X0) X2) = (σ (τ (k (M.op (M.op X0 X1) X0) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11 (k (M.op (M.op X0 X3) X0) X2)
       have i₂ := eq18759 X0 X1 X3 X2
       grind)
    | (have i₁ := eq11 (k (M.op (M.op X0 X3) X0) X2)
       have i₂ := eq18759 X0 X3 X1 X2
       grind)
    | exact superpose eq18759 eq11
    | exact resolve eq11 eq18759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18759
  have eq94514 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 X1) X0) X2) = (k (M.op (M.op X0 X3) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq94327 X0 X3 X2 X1
       have i₂ := eq11 (k (M.op (M.op X0 X3) X0) X2)
       grind)
    | exact superpose eq11 eq94327
    | exact resolve eq94327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94327
  have eq96294 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) X0) (M.op (M.op X0 X2) X0)) = (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14445 (M.op (M.op X0 X2) X0)
       have i₂ := eq94514 X0 X2 (M.op (M.op X0 X2) X0) X1
       grind)
    | (have i₁ := eq14445 (M.op (M.op X0 X2) X0)
       have i₂ := eq94514 X0 X1 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq94514 eq14445
    | exact resolve eq14445 eq94514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94514
  have eq96384 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X1) X0) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq96294 X0 X1 X2
       have i₂ := eq92 X0 X2 (M.op X0 X2)
       grind)
    | exact superpose eq92 eq96294
    | exact resolve eq96294 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96294
  have eq97209 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11538 (M.op (M.op X0 X1) X0) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq96384 X0 X1 x
       grind)
    | exact superpose eq96384 eq11538
    | exact resolve eq11538 eq96384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11538 eq96384
  have eq98644 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq97209 (τ X1) X0
       grind)
    | exact superpose eq97209 eq18
    | (have j1 := eq97209 (τ X1) X0
       grind)
    | exact resolve eq18 eq97209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq98700 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq97209 (σ X1) (σ X0)
       grind)
    | exact superpose eq97209 eq15
    | (have j1 := eq97209 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq97209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97209
  have eq111568 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98644 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98644
    | exact resolve eq98644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98644
  have eq111928 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq111568 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq111568
    | (have j0 := eq111568 X0 X1
       grind)
    | exact resolve eq111568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111568
  have eq428690 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98700 x y
       grind)
    | exact superpose eq98700 eq16
    | (have j1 := eq98700 x y
       grind)
    | exact resolve eq16 eq98700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429189 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq98700 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98700
  have eq430978 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq429189 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq429189
    | (have j0 := eq429189 (τ X0) (τ X1)
       grind)
    | exact resolve eq429189 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431125 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq430978 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq430978
    | (have j0 := eq430978 X0 X1
       grind)
    | exact resolve eq430978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430978
  have eq431227 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq431125 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431125
    | (have j0 := eq431125 X0 X1
       grind)
    | exact resolve eq431125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431125
  have eq431272 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431227 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq431227
    | (have j0 := eq431227 X0 X1
       grind)
    | exact resolve eq431227 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431227
  have eq431297 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431272 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431272
    | (have j0 := eq431272 X0 X1
       grind)
    | exact resolve eq431272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431272
  have eq431410 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq431297 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq431297
    | (have j0 := eq431297 (τ X0) (τ X1)
       grind)
    | exact resolve eq431297 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq431297
  have eq434759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq428690
       have i₂ := eq111928 y x
       grind)
    | exact superpose eq111928 eq428690
    | (have j1 := eq111928 (σ y) (σ x)
       grind)
    | (have r₁ := eq428690
       have r₂ := eq111928 y x
       grind)
    | exact resolve eq428690 eq111928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111928
  have eq434762 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq434759
  have eq436934 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1164 x y x
       have i₂ := eq434762
       grind)
    | exact superpose eq434762 eq1164
    | exact resolve eq1164 eq434762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq437118 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq17891 x X0 (σ y)
       have i₂ := eq436934 X1
       grind)
    | exact superpose eq436934 eq17891
    | (have j1 := eq436934 X1
       grind)
    | exact resolve eq17891 eq436934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17891 eq436934
  have eq437539 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (τ (σ (M.op x x))) ∨ x = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq437118 X0 X1
       have i₂ := eq14582 x
       grind)
    | exact superpose eq14582 eq437118
    | (have j0 := eq437118 X0 X1
       grind)
    | exact resolve eq437118 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437118
  have eq437660 : ∀ X0 X1 : G, x = (M.op x (M.op X1 x)) ∨ (M.op x x) = (M.op (M.op x X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq437539 X0 X1
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq437539
    | (have j0 := eq437539 X0 X1
       grind)
    | exact resolve eq437539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437539
  have eq439564 : ∀ X0 : G, (M.op x x) = (M.op (k x x) x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq2061 x x
       have i₂ := eq437660 X0 (k x x)
       grind)
    | exact superpose eq437660 eq2061
    | (have j0 := eq2061 x x
       have j1 := eq437660 X0 x
       grind)
    | exact resolve eq2061 eq437660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061 eq437660
  have eq439836 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) x) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq439564 X0
       have i₂ := eq14445 x
       grind)
    | exact superpose eq14445 eq439564
    | (have j0 := eq439564 x
       grind)
    | exact resolve eq439564 eq14445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14445 eq439564
  have eq439854 : x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have j0 := eq439836 x
       have j1 := eq12768 x x
       grind)
    | (have r₁ := eq439836 x
       have r₂ := eq12768 x x
       grind)
    | (have r₁ := eq439836 x
       have r₂ := eq12768 x x
       grind)
    | exact resolve eq439836 eq12768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12768 eq439836
  have eq439898 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq14551 x
       have i₂ := eq439854
       grind)
    | exact superpose eq439854 eq14551
    | (have j0 := eq14551 x
       grind)
    | exact resolve eq14551 eq439854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14551 eq439854
  have eq440200 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by grind
  clear eq439898
  have eq440323 : (σ x) = (σ (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq440200
       have i₂ := eq14582 x
       grind)
    | exact superpose eq14582 eq440200
    | exact resolve eq440200 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440200
  have eq445692 : ∀ X0 : G, (M.op (M.op x x) (M.op (M.op (M.op x x) X0) (M.op x x))) = (τ (M.op (σ x) (σ (M.op (M.op (M.op x x) X0) (M.op x x))))) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    intro X0
    first
    | (have i₁ := eq20392 (M.op x x) X0
       have i₂ := eq440323
       grind)
    | exact superpose eq440323 eq20392
    | exact resolve eq20392 eq440323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20392 eq440323
  have eq445816 : (M.op (M.op x x) x) = (τ (M.op (σ x) (σ x))) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq445692 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq445692
    | exact resolve eq445692 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445692
  have eq445989 : (M.op (M.op x x) x) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq445816
       have i₂ := eq14582 x
       grind)
    | exact superpose eq14582 eq445816
    | exact resolve eq445816 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445816
  have eq446038 : (M.op x x) = (M.op (M.op x x) x) ∨ (M.op x x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq445989
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq445989
    | exact resolve eq445989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445989
  have eq446039 : (M.op x x) = (M.op (M.op x x) x) := by grind
  clear eq446038
  have eq447659 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x x) (M.op x X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq611 x x X0
       have i₂ := eq446039
       grind)
    | exact superpose eq446039 eq611
    | exact resolve eq611 eq446039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq447692 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ (M.op x x)) (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20852 x x X0
       have i₂ := eq446039
       grind)
    | exact superpose eq446039 eq20852
    | exact resolve eq20852 eq446039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20852
  have eq447764 : ∀ X0 : G, x = (M.op (M.op x x) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x x X0
       have i₂ := eq446039
       grind)
    | exact superpose eq446039 eq9
    | exact resolve eq9 eq446039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453158 : ∀ X0 X1 : G, (M.op (M.op x x) X0) = (M.op (M.op (M.op x (M.op (M.op x x) X0)) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1676 (M.op x x) X0 X1
       have i₂ := eq447764 x
       grind)
    | exact superpose eq447764 eq1676
    | exact resolve eq1676 eq447764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447764
  have eq483956 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1676 x X0 X0
       have i₂ := eq447659 X0
       grind)
    | exact superpose eq447659 eq1676
    | exact resolve eq1676 eq447659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676 eq447659
  have eq486788 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k (M.op x X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op x X0) X0
       have i₂ := eq483956 X0
       grind)
    | exact superpose eq483956 eq13
    | (have j0 := eq13 (M.op x X0) X0
       grind)
    | (have r₁ := eq13 (M.op x X0) X0
       have r₂ := eq483956 X0
       grind)
    | exact resolve eq13 eq483956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483956
  have eq487053 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq486788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486788
  have eq538356 : ∀ X0 : G, (σ (M.op x X0)) ≠ (σ (M.op x X0)) ∨ (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq429189 (M.op x X0) X0
       have i₂ := eq487053 X0
       grind)
    | exact superpose eq487053 eq429189
    | (have j0 := eq429189 (M.op x X0) X0
       have j1 := eq487053 X0
       grind)
    | exact resolve eq429189 eq487053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429189 eq487053
  have eq538491 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq538356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538356
  have eq576113 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq15193 x X0 X0
       have i₂ := eq447692 X0
       grind)
    | exact superpose eq447692 eq15193
    | exact resolve eq15193 eq447692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15193 eq447692
  have eq578064 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (M.op (σ x) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 (M.op (σ x) X0) X0
       have i₂ := eq576113 X0
       grind)
    | exact superpose eq576113 eq13
    | (have j0 := eq13 (M.op (σ x) X0) X0
       grind)
    | (have r₁ := eq13 (M.op (σ x) X0) X0
       have r₂ := eq576113 X0
       grind)
    | exact resolve eq13 eq576113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576113
  have eq578340 : ∀ X0 : G, (M.op (σ x) X0) = (k (M.op (σ x) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq578064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578064
  have eq645870 : ∀ X0 : G, (τ (M.op (σ x) X0)) ≠ (τ (M.op (σ x) X0)) ∨ (τ (M.op (σ x) X0)) = (M.op (τ (M.op (σ x) X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq431410 (M.op (σ x) X0) X0
       have i₂ := eq578340 X0
       grind)
    | exact superpose eq578340 eq431410
    | (have j0 := eq431410 (M.op (σ x) X0) X0
       have j1 := eq578340 X0
       grind)
    | exact resolve eq431410 eq578340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431410 eq578340
  have eq646009 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (M.op (τ (M.op (σ x) X0)) (τ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq645870 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645870
  have eq675715 : ∀ X0 : G, (M.op (M.op x x) X0) = (M.op (M.op (M.op x x) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq453158 X0 X0
       have i₂ := eq615 x X0
       grind)
    | exact superpose eq615 eq453158
    | exact resolve eq453158 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq453158
  have eq691066 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq538491 y
       have i₂ := eq434762
       grind)
    | exact superpose eq434762 eq538491
    | (have j0 := eq538491 y
       grind)
    | exact resolve eq538491 eq434762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434762 eq538491
  have eq691516 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq691066
  have eq692467 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq691516
       grind)
    | exact superpose eq691516 eq16
    | exact resolve eq16 eq691516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1599973 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq646009 (σ y)
       have i₂ := eq691516
       grind)
    | exact superpose eq691516 eq646009
    | (have j0 := eq646009 (σ y)
       grind)
    | exact resolve eq646009 eq691516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646009 eq691516
  have eq1601171 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1599973
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1599973
    | exact resolve eq1599973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599973
  have eq1601637 : x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1601171
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1601171
    | exact resolve eq1601171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601171
  have eq1601951 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1601637
       have i₂ := eq14582 y
       grind)
    | exact superpose eq14582 eq1601637
    | exact resolve eq1601637 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601637
  have eq1606083 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq692467
       have i₂ := eq1601951
       grind)
    | exact superpose eq1601951 eq692467
    | exact resolve eq692467 eq1601951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692467 eq1601951
  have eq1606397 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq1606083
  have eq1606398 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq1606397
  have eq1608590 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1606398
       grind)
    | exact superpose eq1606398 eq10
    | exact resolve eq10 eq1606398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606398
  have eq1609434 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1608590
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1608590
    | exact resolve eq1608590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608590
  have eq1609435 : y = (M.op y y) := by grind
  clear eq1609434
  have eq1609617 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq1609435
       grind)
    | exact superpose eq1609435 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq1609435
       grind)
    | exact resolve eq12 eq1609435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1609668 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14466 y X0
       have i₂ := eq1609435
       grind)
    | exact superpose eq1609435 eq14466
    | (have j0 := eq14466 y X0
       grind)
    | exact resolve eq14466 eq1609435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14466
  have eq1609691 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15202 y x
       have i₂ := eq1609435
       grind)
    | exact superpose eq1609435 eq15202
    | exact resolve eq15202 eq1609435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15202 eq1609435
  have eq1610127 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1609668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609668
  have eq1610129 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1609617 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609617
  have eq1615729 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (σ y)) = (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq22155 X0 X1 y
       have i₂ := eq1610129 (M.op (τ (M.op X0 X0)) (τ X0))
       grind)
    | exact superpose eq1610129 eq22155
    | exact resolve eq22155 eq1610129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22155
  have eq1615918 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq428690
       have i₂ := eq1610129 x
       grind)
    | exact superpose eq1610129 eq428690
    | exact resolve eq428690 eq1610129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428690 eq1610129
  have eq1615922 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1615918
  have eq1616087 : ∀ X0 X1 : G, (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) y)) = (M.op (M.op (M.op X0 X1) X0) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1615729 X0 X1
       have i₂ := eq1610127 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq1610127 eq1615729
    | exact resolve eq1615729 eq1610127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610127 eq1615729
  have eq1616343 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1615922
       grind)
    | exact superpose eq1615922 eq16
    | exact resolve eq16 eq1615922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1616457 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ y) X0) (σ y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ y) X0 (σ x)
       have i₂ := eq1615922
       grind)
    | exact superpose eq1615922 eq92
    | exact resolve eq92 eq1615922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1615922
  have eq1616956 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1616457 x
       have i₂ := eq1609691 x
       grind)
    | exact superpose eq1609691 eq1616457
    | exact resolve eq1616457 eq1609691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609691 eq1616457
  have eq1620043 : (σ x) = (M.op (M.op (τ (M.op (σ (σ x)) (M.op (σ (M.op (σ x) (σ x))) (σ (σ x))))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq19736 (σ x) (σ y)
       have i₂ := eq1616956
       grind)
    | exact superpose eq1616956 eq19736
    | exact resolve eq19736 eq1616956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19736 eq1616956
  have eq1620378 : (σ x) = (M.op (M.op (M.op (σ x) (τ (M.op (σ (M.op (σ x) (σ x))) (σ (σ x))))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq1620043
       have i₂ := eq19745 (σ x)
       grind)
    | exact superpose eq19745 eq1620043
    | exact resolve eq1620043 eq19745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19745 eq1620043
  have eq1620675 : (σ x) = (σ (M.op (M.op (τ (M.op (σ x) (σ x))) (τ (σ x))) y)) := by
    first
    | (have i₁ := eq1620378
       have i₂ := eq1616087 (σ x) (τ (M.op (σ (M.op (σ x) (σ x))) (σ (σ x))))
       grind)
    | exact superpose eq1616087 eq1620378
    | exact resolve eq1620378 eq1616087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616087 eq1620378
  have eq1620891 : (σ x) = (σ (M.op (M.op (τ (M.op (σ x) (σ x))) x) y)) := by
    first
    | (have i₁ := eq1620675
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1620675
    | exact resolve eq1620675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620675
  have eq1621063 : (σ x) = (σ (M.op (M.op (τ (σ (M.op x x))) x) y)) := by
    first
    | (have i₁ := eq1620891
       have i₂ := eq14582 x
       grind)
    | exact superpose eq14582 eq1620891
    | exact resolve eq1620891 eq14582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14582 eq1620891
  have eq1621185 : (σ x) = (σ (M.op (M.op (M.op x x) x) y)) := by
    first
    | (have i₁ := eq1621063
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq1621063
    | exact resolve eq1621063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621063
  have eq1621254 : (σ x) = (σ (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq1621185
       have i₂ := eq446039
       grind)
    | exact superpose eq446039 eq1621185
    | exact resolve eq1621185 eq446039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446039 eq1621185
  have eq1633754 : (τ (σ x)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq10 (M.op (M.op x x) y)
       have i₂ := eq1621254
       grind)
    | exact superpose eq1621254 eq10
    | exact resolve eq10 eq1621254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621254
  have eq1634633 : x = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1633754
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1633754
    | exact resolve eq1633754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633754
  have eq1635439 : x = (M.op x y) := by
    first
    | (have i₁ := eq675715 y
       have i₂ := eq1634633
       grind)
    | exact superpose eq1634633 eq675715
    | exact resolve eq675715 eq1634633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675715 eq1634633
  have eq1637526 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1616343
       have i₂ := eq1635439
       grind)
    | exact superpose eq1635439 eq1616343
    | exact resolve eq1616343 eq1635439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616343 eq1635439
  have eq1637835 : False := by grind
  exact eq1637835

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxy_pxx_pxy_Equation2046 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq34 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X0) = X1 ∨ (k (M.op (M.op X0 X0) X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X0 X0) X0) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq67 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 X1) X1
       have i₂ := eq26 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq34 (M.op X1 X0) X0
       have r₂ := eq26 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq34
  have eq161 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X1) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq170 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq193 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq170 x y
       grind)
    | exact superpose eq170 eq16
    | (have j1 := eq170 x y
       grind)
    | exact resolve eq16 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq170 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq899 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq193
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq193
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq193
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq193
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq193 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq900 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq899
  have eq3275 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq198 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq198
    | (have j0 := eq198 (τ X0) (τ X1)
       grind)
    | exact resolve eq198 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3305 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3275 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3275
    | (have j0 := eq3275 X0 X1
       grind)
    | exact resolve eq3275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3319 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3305 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq3305
    | (have j0 := eq3305 X0 X1
       grind)
    | exact resolve eq3305 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3305
  have eq3329 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3319 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3319
    | (have j0 := eq3319 X0 X1
       grind)
    | exact resolve eq3319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3333 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3329
    | (have j0 := eq3329 X0 X1
       grind)
    | exact resolve eq3329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3329
  have eq3336 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3333 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq3333
    | (have j0 := eq3333 X0 X1
       grind)
    | exact resolve eq3333 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq3333
  have eq3338 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3336 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3336
    | (have j0 := eq3336 X0 X1
       grind)
    | exact resolve eq3336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3340 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3338 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3338
    | (have j0 := eq3338 X0 X1
       grind)
    | exact resolve eq3338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3338
  have eq3754 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (k (σ (M.op (M.op (M.op X0 (τ X1)) (M.op X0 (τ X1))) (M.op X0 (τ X1)))) X1) ∨ (τ X1) = (M.op (M.op (M.op X0 (τ X1)) (M.op X0 (τ X1))) (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (M.op (M.op (M.op X0 (τ X1)) (M.op X0 (τ X1))) (M.op X0 (τ X1)))
       have i₂ := eq161 X0 (τ X1)
       grind)
    | exact superpose eq161 eq19
    | (have j1 := eq161 X0 (τ X1)
       grind)
    | exact resolve eq19 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq161
  have eq11326 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq900
       grind)
    | exact superpose eq900 eq16
    | exact resolve eq16 eq900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq11327 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq11326
       have r₂ := eq22 x
       grind)
    | exact resolve eq11326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11326
  have eq45020 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (k (σ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0))) (σ X0)) ∨ (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3754 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3754
    | exact resolve eq3754 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq45264 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) = X0 ∨ (σ (M.op X1 X0)) = (σ (k (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45020 X0 X1
       have i₂ := eq15 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)) X0
       grind)
    | exact superpose eq15 eq45020
    | (have j0 := eq45020 X0 X1
       grind)
    | exact resolve eq45020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45020
  have eq936243 : y = (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) ∨ (σ (M.op x x)) = (σ (k (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45264 y x
       have i₂ := eq11327
       grind)
    | exact superpose eq11327 eq45264
    | exact resolve eq45264 eq11327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11327 eq45264
  have eq937065 : x = y ∨ (σ (M.op x x)) = (σ (k (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq936243
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq936243
    | exact resolve eq936243 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936243
  have eq937453 : (σ (k x y)) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq937065
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq937065
    | exact resolve eq937065 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937065
  have eq937763 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq198 x y
       grind)
    | (have r₁ := eq937453
       have r₂ := eq198 x y
       grind)
    | exact resolve eq937453 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq937453
  have eq938466 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq937763
       grind)
    | exact superpose eq937763 eq16
    | exact resolve eq16 eq937763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937763
  have eq938467 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq938466
       have r₂ := eq22 x
       grind)
    | exact resolve eq938466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938466
  have eq938469 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq938467
       grind)
    | exact superpose eq938467 eq16
    | exact resolve eq16 eq938467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938470 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq67 x (σ y)
       have i₂ := eq938467
       grind)
    | exact superpose eq938467 eq67
    | (have j0 := eq67 x (σ y)
       grind)
    | (have r₁ := eq67 x (σ y)
       have r₂ := eq938467
       grind)
    | exact resolve eq67 eq938467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq938467
  have eq938740 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq938470
  have eq938741 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) := by grind
  clear eq938740
  have eq938856 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq938741
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq938741
    | exact resolve eq938741 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938741
  have eq940982 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq938856
       grind)
    | exact superpose eq938856 eq10
    | exact resolve eq10 eq938856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938856
  have eq941797 : x = y ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq940982
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq940982
    | exact resolve eq940982 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940982
  have eq943301 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq941797
       grind)
    | exact superpose eq941797 eq16
    | exact resolve eq16 eq941797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941797
  have eq943302 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq943301
       have r₂ := eq22 x
       grind)
    | exact resolve eq943301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943301
  have eq945280 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq943302
       grind)
    | exact superpose eq943302 eq10
    | exact resolve eq10 eq943302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943302
  have eq946109 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq945280
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq945280
    | exact resolve eq945280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945280
  have eq946173 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq3340 x y
       have i₂ := eq946109
       grind)
    | exact superpose eq946109 eq3340
    | (have j0 := eq3340 x y
       grind)
    | (have r₁ := eq3340 x y
       have r₂ := eq946109
       grind)
    | exact resolve eq3340 eq946109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340 eq946109
  have eq946209 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq946173
  have eq948174 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq946209
       grind)
    | exact superpose eq946209 eq16
    | exact resolve eq16 eq946209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946209
  have eq948177 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq948174
       have r₂ := eq22 x
       grind)
    | exact resolve eq948174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948174
  have eq948178 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq938469
       have i₂ := eq948177
       grind)
    | exact superpose eq948177 eq938469
    | exact resolve eq938469 eq948177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938469
  have eq948338 : (σ x) = (σ y) := by grind
  clear eq948178
  have eq948362 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq948338
       grind)
    | exact superpose eq948338 eq16
    | exact resolve eq16 eq948338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948338
  have eq949181 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq948362
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq948362
    | exact resolve eq948362 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq948362
  have eq949205 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq949181
       have i₂ := eq948177
       grind)
    | exact superpose eq948177 eq949181
    | exact resolve eq949181 eq948177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948177 eq949181
  have eq949206 : False := by grind
  exact eq949206

/-- `Equation2046`: `x = ((x ◇ x) ◇ y) ◇ (z ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation2046 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2046 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2046.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq44 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X2 (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op x X0) X2
       have i₂ := eq9 X0 (M.op X0 X0) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq105
    | (have j0 := eq105 X0 X1
       grind)
    | exact resolve eq105 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq140 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X0) x
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq44
    | exact resolve eq44 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq190 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (M.op X0 X0) X1
       have i₂ := eq9 X0 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq45
    | exact resolve eq45 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq211 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq190 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq190 X1 X1
       grind)
    | exact superpose eq190 eq9
    | exact resolve eq9 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq343 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X2) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) X0) X1
       have i₂ := eq211 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq211 eq50
    | exact resolve eq50 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq211
  have eq577 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108 x y
       grind)
    | exact superpose eq108 eq16
    | (have j1 := eq108 x y
       grind)
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq721 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X2) X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq343 X0 X2 (M.op x (σ (M.op X0 X0)))
       have i₂ := eq140 X0 x
       grind)
    | exact superpose eq140 eq343
    | exact resolve eq343 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq343
  have eq5392 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq577
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq577
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq577
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq577
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq577 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq5393 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5392
  have eq54603 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5393
       grind)
    | exact superpose eq5393 eq16
    | exact resolve eq16 eq5393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5393
  have eq54604 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq54603
       have r₂ := eq23 x
       grind)
    | exact resolve eq54603 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54603
  have eq54606 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq54604
       grind)
    | exact superpose eq54604 eq10
    | exact resolve eq10 eq54604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54604
  have eq54710 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq54606
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq54606
    | exact resolve eq54606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54606
  have eq54718 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54710
       grind)
    | exact superpose eq54710 eq16
    | exact resolve eq16 eq54710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54710
  have eq54719 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq54718
       have r₂ := eq23 x
       grind)
    | exact resolve eq54718 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54718
  have eq55113 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq54719
       grind)
    | exact superpose eq54719 eq10
    | exact resolve eq10 eq54719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54719
  have eq55224 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq55113
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq55113
    | exact resolve eq55113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55113
  have eq55225 : x = (M.op y y) := by grind
  clear eq55224
  have eq55357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq721 y y
       have i₂ := eq55225
       grind)
    | exact superpose eq55225 eq721
    | exact resolve eq721 eq55225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq55225
  have eq55430 : False := by grind
  exact eq55430

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  clear eq25 eq36
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq88
    | exact resolve eq88 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq265 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq493 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X0
       have i₂ := eq379 X0 (σ X0)
       grind)
    | (have i₁ := eq73 X0 X0
       have i₂ := eq379 (σ X0) X1
       grind)
    | exact superpose eq379 eq73
    | exact resolve eq73 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq520 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq537 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq265
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq12369 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq520 X0 (τ X1)
       grind)
    | exact superpose eq520 eq35
    | (have j1 := eq520 X0 (τ X1)
       grind)
    | exact resolve eq35 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq520
  have eq12456 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12369 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12369
    | (have j0 := eq12369 X0 X1
       grind)
    | exact resolve eq12369 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12369
  have eq12478 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12456 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12456
    | (have j0 := eq12456 X0 X1
       grind)
    | exact resolve eq12456 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12456
  have eq13101 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12478 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12478
  have eq13175 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13101 X1 (τ X0)
       have i₂ := eq537 X0 X0
       grind)
    | exact superpose eq537 eq13101
    | (have j0 := eq13101 X1 (τ X0)
       grind)
    | exact resolve eq13101 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq18754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq18755 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18754
    | exact resolve eq18754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18754
  have eq18766 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18755
       have r₂ := eq28
       grind)
    | exact resolve eq18755 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18755
  have eq18768 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq18766
       have i₂ := eq379 X0 sF3
       grind)
    | (have i₁ := eq18766
       have i₂ := eq379 sF3 x
       grind)
    | exact superpose eq379 eq18766
    | exact resolve eq18766 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18766
  have eq18877 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq18768 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18768
  have eq18878 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18877
  have eq18886 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq18878
       have i₂ := eq379 X0 sF2
       grind)
    | (have i₁ := eq18878
       have i₂ := eq379 sF2 x
       grind)
    | exact superpose eq379 eq18878
    | exact resolve eq18878 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18878
  have eq18943 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq18886 X1
       have i₂ := eq379 X0 y
       grind)
    | (have i₁ := eq18886 X1
       have i₂ := eq379 y X0
       grind)
    | exact superpose eq379 eq18886
    | (have j0 := eq18886 X1
       grind)
    | exact resolve eq18886 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq18886
  have eq19315 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq18943 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18943
  have eq19317 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq19315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19315
  have eq19332 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq19803 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq19332 X0
       grind)
    | exact superpose eq19332 eq44
    | (have j1 := eq19332 X0
       grind)
    | exact resolve eq44 eq19332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq19332
  have eq21357 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq19803 X0
       have i₂ := eq19317 X1
       grind)
    | exact superpose eq19317 eq19803
    | (have j0 := eq19803 X0
       have j1 := eq19317 X0
       grind)
    | exact resolve eq19803 eq19317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19317 eq19803
  have eq21466 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq21357 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21357
    | (have j0 := eq21357 X0 X0
       grind)
    | exact resolve eq21357 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21357
  have eq21468 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq21466 X1 X1
       have j1 := eq13101 X1 (σ x)
       grind)
    | (have r₁ := eq21466 X0 X1
       have r₂ := eq13101 X0 (σ x)
       grind)
    | exact resolve eq21466 eq13101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13101 eq21466
  have eq21593 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21468 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21468
  have eq21594 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21593 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21593
  have eq21644 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    grind
  have eq21648 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq21594 x
       grind)
    | exact superpose eq21594 eq63
    | exact resolve eq63 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21798 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21648
       have i₂ := eq21594 sF2
       grind)
    | exact superpose eq21594 eq21648
    | exact resolve eq21648 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21648
  have eq21851 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21798
       have i₂ := eq21594 sF2
       grind)
    | exact superpose eq21594 eq21798
    | exact resolve eq21798 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21798
  have eq21916 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq21851 eq13175
    | (have j0 := eq13175 (σ x) X0
       grind)
    | exact resolve eq13175 eq21851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13175 eq21851
  have eq21919 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq21916 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21916
  have eq21934 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq21919
    | exact resolve eq21919 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21919
  have eq21954 : x = (σ x) := by
    first
    | (have i₁ := eq21934 x
       have i₂ := eq21594 x
       grind)
    | exact superpose eq21594 eq21934
    | exact resolve eq21934 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21594 eq21934
  have eq21963 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq21954 eq27
    | exact resolve eq27 eq21954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22285 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq21954 eq21644
    | exact resolve eq21644 eq21954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21644
  have eq22710 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq22285 y
       grind)
    | exact superpose eq22285 eq45
    | exact resolve eq45 eq22285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq22748 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq21954 eq22710
    | exact resolve eq22710 eq21954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21954 eq22710
  have eq22827 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq22748
       have i₂ := eq22285 sF3
       grind)
    | exact superpose eq22285 eq22748
    | exact resolve eq22748 eq22285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22285 eq22748
  have eq22896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21963 eq22827
    | exact resolve eq22827 eq21963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21963 eq22827
  have eq22942 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22896
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22896
    | exact resolve eq22896 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22896
  have eq22975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22942
    | exact resolve eq22942 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22942
  have eq22996 : False := by grind
  exact eq22996

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X1) = (k X0 X2) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X1 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X2
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X1) = (k X0 X2) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq44 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq1151 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1152 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1155 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1152 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1152 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1152 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1365 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1155 (σ X1) (σ X0)
       grind)
    | exact superpose eq1155 eq15
    | exact resolve eq15 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1368 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1365 X0 X1
       have i₂ := eq1155 X1 X0
       grind)
    | exact superpose eq1155 eq1365
    | exact resolve eq1365 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1365
  have eq1372 : False := by grind
  exact eq1372

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pyy_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X3)) = X2 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X3)) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq47 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq129 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq20 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq20 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq233 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (M.op X0 X1) X2 x
       have i₂ := eq59 X0 X1 (M.op X0 X1) x
       grind)
    | exact superpose eq59 eq20
    | (have j1 := eq59 X0 X1 X2 x
       grind)
    | exact resolve eq20 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq59
  have eq1819 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X1) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X2 X1
       have i₂ := eq129 X0 X1
       grind)
    | (have i₁ := eq178 X2 X1
       have i₂ := eq129 X1 X0
       grind)
    | exact superpose eq129 eq178
    | (have j0 := eq178 X2 X1
       grind)
    | (have r₁ := eq178 X0 X0
       have r₂ := eq129 X0 X0
       grind)
    | (have r₁ := eq178 X1 X1
       have r₂ := eq129 X1 X1
       grind)
    | exact resolve eq178 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq178
  have eq1876 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) := by
    intro X1 X2
    first
    | (have j0 := eq1819 x X1 X2
       have j1 := eq233 X2 X1 X2
       grind)
    | (have r₁ := eq1819 X2 X1 x
       have r₂ := eq233 x X1 X2
       grind)
    | (have r₁ := eq1819 X1 X2 X2
       have r₂ := eq233 X1 X1 X2
       grind)
    | exact resolve eq1819 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233 eq1819
  have eq13420 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1876 (σ X1) (σ X0)
       grind)
    | exact superpose eq1876 eq15
    | exact resolve eq15 eq1876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13420 X0 X1
       have i₂ := eq1876 X1 X0
       grind)
    | exact superpose eq1876 eq13420
    | exact resolve eq13420 eq1876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876 eq13420
  have eq13450 : False := by grind
  exact eq13450

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (k X3 X2) = (M.op X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X2 X2))
       have r₂ := eq21 X0 (M.op (M.op X0 X0) (M.op X2 X2)) X2
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq21 X1 X1 X1
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (M.op X3 X3) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X3
       have i₂ := eq21 X0 X2 X1
       grind)
    | (have i₁ := eq14 (M.op X2 X2) X1
       have i₂ := eq21 X2 X1 X2
       grind)
    | exact superpose eq21 eq14
    | (have j0 := eq14 X3 X3
       grind)
    | exact resolve eq14 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq106 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq93 X0 X1 X2 X3
       have j1 := eq12 X2 X3
       grind)
    | (have r₁ := eq93 X0 X0 X2 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq93 X0 X1 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have r₂ := eq12 X0 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | (have r₁ := eq93 X0 X1 X2 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq112 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) := by
    intro X2 X3
    first
    | (have j0 := eq106 x x X2 X3
       have j1 := eq91 x x X3 X2
       grind)
    | (have r₁ := eq106 x x X2 X2
       have r₂ := eq91 x x X2 X3
       grind)
    | (have r₁ := eq106 x x X2 (M.op (M.op x x) (M.op x x))
       have r₂ := eq91 x x (M.op (M.op x x) (M.op x x)) X3
       grind)
    | (have r₁ := eq106 x x (M.op x x) (M.op x x)
       have r₂ := eq91 x x (k (M.op x x) (M.op x x)) X3
       grind)
    | exact resolve eq106 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq106
  have eq337 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq112 (σ X1) (σ X0)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq112 X1 X0
       grind)
    | exact superpose eq112 eq337
    | exact resolve eq337 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq337
  have eq345 : False := by grind
  exact eq345
