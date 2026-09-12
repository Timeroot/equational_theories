import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq92 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq551 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq2507 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq2542 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2507 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2507
    | (have j0 := eq2507 X0 X1
       grind)
    | exact resolve eq2507 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2507
  have eq2558 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2542 X0 X1
       have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq2542 X1 X0
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq2542 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq92 X0 X1
       grind)
    | exact resolve eq2542 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2542
  have eq2567 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2558 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2558
    | exact resolve eq2558 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2584 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2558 (σ X1) X0
       grind)
    | exact superpose eq2558 eq15
    | (have j1 := eq2558 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq2558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2558
  have eq2620 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq2567 (τ X0) X1
       grind)
    | exact superpose eq2567 eq19
    | (have j1 := eq2567 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq2567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2567
  have eq2874 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2620 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2620
    | exact resolve eq2620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620
  have eq3004 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2874 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2874
    | (have j0 := eq2874 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq2874 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874
  have eq3292 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2584 x y
       grind)
    | exact superpose eq2584 eq16
    | (have j1 := eq2584 x y
       grind)
    | exact resolve eq16 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584
  have eq3312 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3292
       have i₂ := eq3004 x y
       grind)
    | exact superpose eq3004 eq3292
    | (have j1 := eq3004 (σ x) (σ y)
       grind)
    | (have r₁ := eq3292
       have r₂ := eq3004 x y
       grind)
    | (have r₁ := eq3292
       have r₂ := eq3004 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3292
       have r₂ := eq3004 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3292 eq3004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004 eq3292
  have eq3315 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3312
  have eq3318 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3315
       grind)
    | exact superpose eq3315 eq16
    | exact resolve eq16 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3319 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3318
       have r₂ := eq78 x
       grind)
    | exact resolve eq3318 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318
  have eq3320 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3319
       grind)
    | exact superpose eq3319 eq16
    | exact resolve eq16 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3321 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3319
       grind)
    | exact superpose eq3319 eq10
    | exact resolve eq10 eq3319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3384 : x = y := by
    first
    | (have i₁ := eq3321
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3321
    | exact resolve eq3321 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3385 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3320
       have i₂ := eq78 x
       grind)
    | exact superpose eq78 eq3320
    | exact resolve eq3320 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq3320
  have eq3386 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3385
       have i₂ := eq3384
       grind)
    | exact superpose eq3384 eq3385
    | exact resolve eq3385 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384 eq3385
  have eq3387 : False := by grind
  exact eq3387

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq31 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq31 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq38 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq43
    | (have j0 := eq43 X0 X1
       grind)
    | exact resolve eq43 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq43
  have eq51 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq48 X0 X1
       grind)
    | (have r₁ := eq49 X0 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq49 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq49
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq51 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq51 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq51 X1 X1
       grind)
    | exact resolve eq94 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq94
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq15
    | exact resolve eq15 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq204
    | exact resolve eq204 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq204
  have eq213 : False := by grind
  exact eq213

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq271 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq272 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq274 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq272
    | (have j0 := eq272 X0 X1
       grind)
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq278 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       have j1 := eq270 X0 X1
       grind)
    | (have r₁ := eq274 X0 X1
       have r₂ := eq270 X0 X1
       grind)
    | (have r₁ := eq274 X0 (k X1 X0)
       have r₂ := eq270 X0 X1
       grind)
    | (have r₁ := eq274 X0 X0
       have r₂ := eq270 X0 X0
       grind)
    | exact resolve eq274 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq274
  have eq511 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq278 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq278 x y
       grind)
    | exact superpose eq278 eq16
    | (have j1 := eq278 x y
       grind)
    | exact resolve eq16 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq540 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq511 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq511
    | (have j0 := eq511 X0 X1
       grind)
    | exact resolve eq511 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq511
  have eq541 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq540
    | exact resolve eq540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq600 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq541 (τ X1) X0
       grind)
    | exact superpose eq541 eq18
    | (have j1 := eq541 (τ X1) X0
       grind)
    | exact resolve eq18 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq541
  have eq838 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq600
    | exact resolve eq600 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq891 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq838 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq838
    | (have j0 := eq838 X0 X1
       grind)
    | exact resolve eq838 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq953 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq525
       have i₂ := eq891 y x
       grind)
    | exact superpose eq891 eq525
    | (have j1 := eq891 (σ y) (σ x)
       grind)
    | (have r₁ := eq525
       have r₂ := eq891 y x
       grind)
    | exact resolve eq525 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq953
  have eq960 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq954
  have eq1006 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq525
       have i₂ := eq960
       grind)
    | exact superpose eq960 eq525
    | exact resolve eq525 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq960
  have eq1007 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1006
  have eq1008 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1007
  have eq1021 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1008
  have eq1027 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1021
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1021
    | exact resolve eq1021 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1077 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1027
       grind)
    | exact superpose eq1027 eq16
    | exact resolve eq16 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1077
       have i₂ := eq891 y x
       grind)
    | exact superpose eq891 eq1077
    | (have j1 := eq891 y x
       grind)
    | (have r₁ := eq1077
       have r₂ := eq891 y x
       grind)
    | exact resolve eq1077 eq891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq1118 : y = (M.op x x) := by grind
  clear eq1117
  have eq1125 : (M.op x y) = (k y x) := by grind
  clear eq1118
  have eq1165 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1077
       have i₂ := eq1125
       grind)
    | exact superpose eq1125 eq1077
    | exact resolve eq1077 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq1125
  have eq1168 : False := by grind
  exact eq1168

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pxy_Equation873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq109 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (M.op X1 X1) (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (M.op (τ (τ X0)) (M.op (M.op X1 X1) (τ (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq109
    | exact resolve eq109 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq631 : ∀ X0 X1 : G, (M.op (τ (τ (τ X0))) (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq156
    | exact resolve eq156 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq671 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq679 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq688 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq679
    | (have j0 := eq679 X0 X1
       grind)
    | exact resolve eq679 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq696 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq710 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq946 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ X0)))) (M.op (M.op X1 X1) (τ (τ (τ (τ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq631
    | exact resolve eq631 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1220 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq710 x y
       grind)
    | exact superpose eq710 eq16
    | (have j1 := eq710 x y
       grind)
    | exact resolve eq16 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1373 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ (τ X0))))) (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq946 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq946
    | exact resolve eq946 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq5599 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ (τ (τ X0)))))) (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1373 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq1373
    | exact resolve eq1373 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1373
  have eq5612 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq688 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq688
    | (have j0 := eq688 (σ X0) X1
       grind)
    | exact resolve eq688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq5759 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5612 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5612
    | (have j0 := eq5612 X0 X1
       grind)
    | exact resolve eq5612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612
  have eq5792 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5759 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq5759
    | (have j0 := eq5759 X0 X1
       grind)
    | exact resolve eq5759 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5759
  have eq5815 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5792 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5792
    | (have j0 := eq5792 X0 X1
       grind)
    | exact resolve eq5792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5792
  have eq6853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq5815 x y
       grind)
    | exact superpose eq5815 eq1220
    | (have j1 := eq5815 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq5815 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq5815 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq5815 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1220 eq5815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq5815
  have eq6854 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq6853
  have eq12075 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6854
       grind)
    | exact superpose eq6854 eq16
    | exact resolve eq16 eq6854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6854
  have eq12076 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq12075
       have r₂ := eq22 x
       grind)
    | exact resolve eq12075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12075
  have eq12081 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq12076
       grind)
    | exact superpose eq12076 eq22
    | exact resolve eq22 eq12076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq12164 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12081
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq12081
    | exact resolve eq12081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081
  have eq12165 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq12164
  have eq12250 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq12165
       grind)
    | exact superpose eq12165 eq10
    | exact resolve eq10 eq12165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12339 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12250
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq12250
    | exact resolve eq12250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12340 : (M.op x x) = (M.op y y) := by grind
  clear eq12339
  have eq12574 : ∀ X0 : G, y = (M.op (τ (τ (τ (τ (τ (τ X0)))))) (M.op (M.op x x) (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))) := by
    intro X0
    first
    | (have i₁ := eq5599 X0 y
       have i₂ := eq12340
       grind)
    | exact superpose eq12340 eq5599
    | exact resolve eq5599 eq12340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12340
  have eq12575 : x = y := by
    first
    | (have i₁ := eq12574 x
       have i₂ := eq5599 x x
       grind)
    | exact superpose eq5599 eq12574
    | exact resolve eq12574 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599 eq12574
  have eq12667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12575
       grind)
    | exact superpose eq12575 eq16
    | exact resolve eq16 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575
  have eq12668 : False := by grind
  exact eq12668

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyy_pyx_Equation873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) (M.op X1 X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq109 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (M.op X1 X1) (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (M.op (τ (τ X0)) (M.op (M.op X1 X1) (τ (τ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq109
    | exact resolve eq109 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq631 : ∀ X0 X1 : G, (M.op (τ (τ (τ X0))) (M.op (M.op X1 X1) (τ (τ (τ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq156 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq156
    | exact resolve eq156 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq671 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq679 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq688 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq679 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq679
    | (have j0 := eq679 X0 X1
       grind)
    | exact resolve eq679 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq696 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq710 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq946 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ X0)))) (M.op (M.op X1 X1) (τ (τ (τ (τ (M.op X0 X0))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq631
    | exact resolve eq631 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1220 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq710 x y
       grind)
    | exact superpose eq710 eq16
    | (have j1 := eq710 x y
       grind)
    | exact resolve eq16 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1373 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ (τ X0))))) (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (M.op X0 X0)))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq946 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq946
    | exact resolve eq946 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq5599 : ∀ X0 X1 : G, (M.op (τ (τ (τ (τ (τ (τ X0)))))) (M.op (M.op X1 X1) (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1373 (τ X0) X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq1373
    | exact resolve eq1373 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1373
  have eq5612 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq688
    | (have j0 := eq688 X1 (σ X0)
       grind)
    | exact resolve eq688 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq5692 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5612 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5612
    | (have j0 := eq5612 X0 X1
       grind)
    | exact resolve eq5612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612
  have eq5702 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5692 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq5692
    | (have j0 := eq5692 X0 X1
       grind)
    | exact resolve eq5692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5692
  have eq5707 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5702 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5702
    | (have j0 := eq5702 X0 X1
       grind)
    | exact resolve eq5702 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5702
  have eq6736 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1220
       have i₂ := eq5707 y x
       grind)
    | exact superpose eq5707 eq1220
    | (have j1 := eq5707 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq5707 y x
       grind)
    | (have r₁ := eq1220
       have r₂ := eq5707 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq5707 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1220 eq5707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq5707
  have eq6737 : x = y ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by grind
  clear eq6736
  have eq12075 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6737
       grind)
    | exact superpose eq6737 eq16
    | exact resolve eq16 eq6737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6737
  have eq12076 : (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq12075
       have r₂ := eq22 x
       grind)
    | exact resolve eq12075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12075
  have eq12081 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq12076
       grind)
    | exact superpose eq12076 eq22
    | exact resolve eq22 eq12076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12076
  have eq12164 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq12081
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq12081
    | exact resolve eq12081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081
  have eq12165 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq12164
  have eq12250 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq12165
       grind)
    | exact superpose eq12165 eq10
    | exact resolve eq10 eq12165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12165
  have eq12339 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12250
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq12250
    | exact resolve eq12250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12340 : (M.op x x) = (M.op y y) := by grind
  clear eq12339
  have eq12574 : ∀ X0 : G, y = (M.op (τ (τ (τ (τ (τ (τ X0)))))) (M.op (M.op x x) (τ (τ (τ (τ (τ (τ (M.op X0 X0))))))))) := by
    intro X0
    first
    | (have i₁ := eq5599 X0 y
       have i₂ := eq12340
       grind)
    | exact superpose eq12340 eq5599
    | exact resolve eq5599 eq12340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12340
  have eq12575 : x = y := by
    first
    | (have i₁ := eq12574 x
       have i₂ := eq5599 x x
       grind)
    | exact superpose eq5599 eq12574
    | exact resolve eq12574 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5599 eq12574
  have eq12667 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12575
       grind)
    | exact superpose eq12575 eq16
    | exact resolve eq16 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575
  have eq12668 : False := by grind
  exact eq12668

/-- `Equation873`: `x = y ◇ ((x ◇ x) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law873.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq163 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq169 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq176 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq334 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq176
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq176 x y
       grind)
    | exact superpose eq176 eq16
    | (have j1 := eq176 x y
       grind)
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq352 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq334 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq334
    | (have j0 := eq334 X0 X1
       grind)
    | exact resolve eq334 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq334
  have eq357 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq352
    | exact resolve eq352 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq477 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq340
       have i₂ := eq357 x y
       grind)
    | exact superpose eq357 eq340
    | (have j1 := eq357 (σ x) (σ y)
       grind)
    | (have r₁ := eq340
       have r₂ := eq357 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq340
       have r₂ := eq357 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq340 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq357
  have eq480 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq477
  have eq482 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq480
       grind)
    | exact superpose eq480 eq10
    | exact resolve eq10 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq516 : x = y ∨ x = y := by
    first
    | (have i₁ := eq482
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq482
    | exact resolve eq482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq517 : x = y := by grind
  clear eq516
  have eq566 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq517
       grind)
    | exact superpose eq517 eq16
    | exact resolve eq16 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq567 : False := by grind
  exact eq567

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_Equation882 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq341 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq367 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq372 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq367 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq367 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq367 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq367 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq373 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq341 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq341 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq341 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq380 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq381 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq382 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq373 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq373
    | (have j0 := eq373 X0 X1
       grind)
    | exact resolve eq373 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq386 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       have j1 := eq381 X0 X1
       grind)
    | (have r₁ := eq383 X0 X1
       have r₂ := eq381 X0 X1
       grind)
    | exact resolve eq383 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq383
  have eq387 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq386 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq386
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386 x y
       grind)
    | exact superpose eq386 eq16
    | exact resolve eq16 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq533 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq387 X0 (τ X1)
       grind)
    | exact superpose eq387 eq17
    | exact resolve eq17 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq387
  have eq564 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq533
    | exact resolve eq533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq578 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq564
    | exact resolve eq564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq617 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq399
       have i₂ := eq578 x y
       grind)
    | exact superpose eq578 eq399
    | exact resolve eq399 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq578
  have eq618 : False := by grind
  exact eq618

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_y_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq89 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq173 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq149 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq149 (M.op X0 X0) X0
       grind)
    | exact superpose eq149 eq149
    | exact resolve eq149 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq179 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq173 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq173
    | exact resolve eq173 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | (have j0 := eq64 X1 (τ X0)
       grind)
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq302 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq275
    | (have j0 := eq275 X0 X1
       grind)
    | exact resolve eq275 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq275
  have eq310 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       have j1 := eq89 X1 X0
       grind)
    | (have r₁ := eq302 X1 X0
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq302 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq302
  have eq314 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq310
    | (have j0 := eq310 X0 X1
       grind)
    | exact resolve eq310 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq310
  have eq1419 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq314
    | exact resolve eq314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq314 (σ X1) X0
       grind)
    | exact superpose eq314 eq15
    | (have j1 := eq314 (σ X1) X0
       grind)
    | exact resolve eq15 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq1442 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1431 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq1431
    | (have j0 := eq1431 X0 X1
       grind)
    | exact resolve eq1431 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1431
  have eq19689 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1442 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1442 X0 X1
       grind)
    | exact superpose eq1442 eq10
    | (have j1 := eq1442 X0 X1
       grind)
    | exact resolve eq10 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442
  have eq19770 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19689 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19689
    | (have j0 := eq19689 X0 X1
       grind)
    | exact resolve eq19689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19689
  have eq29736 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19770 x y
       grind)
    | exact superpose eq19770 eq16
    | (have j1 := eq19770 x y
       grind)
    | exact resolve eq16 eq19770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19770
  have eq30146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29736
       have i₂ := eq1419 x y
       grind)
    | exact superpose eq1419 eq29736
    | (have j1 := eq1419 x y
       grind)
    | exact resolve eq29736 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq29736
  have eq30151 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq30146
  have eq30152 : x = (M.op y y) := by grind
  clear eq30151
  have eq30458 : x = (M.op x y) := by
    first
    | (have i₁ := eq173 y
       have i₂ := eq30152
       grind)
    | exact superpose eq30152 eq173
    | exact resolve eq173 eq30152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq30459 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq30152
       grind)
    | exact superpose eq30152 eq179
    | exact resolve eq179 eq30152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq30152
  have eq34304 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30459
       grind)
    | exact superpose eq30459 eq16
    | exact resolve eq16 eq30459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30459
  have eq34425 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq34304
       have i₂ := eq30458
       grind)
    | exact superpose eq30458 eq34304
    | exact resolve eq34304 eq30458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30458 eq34304
  have eq34426 : False := by grind
  exact eq34426
