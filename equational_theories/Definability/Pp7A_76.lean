import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_pxy_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq371 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq374 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq390 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq387 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq387 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq387 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq387 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq387 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq402 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq389 (M.op X0 X1) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq389 X0 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq389 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq389 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq405 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq371
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq371 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq408 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       have j1 := eq390 X1 X0
       grind)
    | (have r₁ := eq402 X0 X1
       have r₂ := eq390 X0 X1
       grind)
    | (have r₁ := eq402 X1 X0
       have r₂ := eq390 X0 X1
       grind)
    | (have r₁ := eq402 X1 X1
       have r₂ := eq390 (k X1 X1) X1
       grind)
    | exact resolve eq402 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq402
  have eq409 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq405
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq405
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq516 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq408
    | exact resolve eq408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq408 X1 (τ X0)
       grind)
    | exact superpose eq408 eq17
    | (have j1 := eq408 X1 (τ X0)
       grind)
    | exact resolve eq17 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq408
  have eq1478 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq541 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq541
    | exact resolve eq541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq1550 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1478 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1478
    | (have j0 := eq1478 X0 X1
       grind)
    | exact resolve eq1478 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq3151 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq409
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq409
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq409 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3152 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3151
  have eq3153 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq3152
       have r₂ := eq12 x y
       grind)
    | exact resolve eq3152 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3152
  have eq3488 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq516 X1 X0
       grind)
    | exact superpose eq516 eq10
    | (have j1 := eq516 X1 X0
       grind)
    | exact resolve eq10 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3488 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3488
    | (have j0 := eq3488 X0 X1
       grind)
    | exact resolve eq3488 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3632 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3537 y x
       grind)
    | exact superpose eq3537 eq16
    | (have j1 := eq3537 y x
       grind)
    | exact resolve eq16 eq3537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537
  have eq3709 : y = (k x y) := by
    first
    | (have j1 := eq1550 x y
       grind)
    | (have r₁ := eq3632
       have r₂ := eq1550 x y
       grind)
    | exact resolve eq3632 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq3632
  have eq4731 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq516 x y
       have i₂ := eq3153
       grind)
    | exact superpose eq3153 eq516
    | (have j0 := eq516 x y
       grind)
    | exact resolve eq516 eq3153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516 eq3153
  have eq4732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq4731
       have r₂ := eq409
       grind)
    | exact resolve eq4731 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq4731
  have eq4734 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have r₁ := eq4732
       have r₂ := eq16
       grind)
    | exact resolve eq4732 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4732
  have eq4735 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4734
       have i₂ := eq3709
       grind)
    | exact superpose eq3709 eq4734
    | exact resolve eq4734 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4734
  have eq4737 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4735
       grind)
    | exact superpose eq4735 eq16
    | exact resolve eq16 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq4783 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq4737
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq4737
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq4737 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4784 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq4783
  have eq4785 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq4784
       have r₂ := eq12 x y
       grind)
    | exact resolve eq4784 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4784
  have eq4786 : y = (M.op x y) := by
    first
    | (have i₁ := eq4785
       have i₂ := eq3709
       grind)
    | exact superpose eq3709 eq4785
    | exact resolve eq4785 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709 eq4785
  have eq4787 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4737
       have i₂ := eq4786
       grind)
    | exact superpose eq4786 eq4737
    | exact resolve eq4737 eq4786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737 eq4786
  have eq4803 : False := by grind
  exact eq4803

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pxy_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq234 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq91
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq258 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq234 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq234
    | (have j0 := eq234 X0 X1
       grind)
    | exact resolve eq234 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq234
  have eq263 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq258 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq258 X0 (M.op (τ X0) (τ X0))
       have r₂ := eq12 X0 (σ (M.op (τ X0) (τ X0)))
       grind)
    | (have r₁ := eq258 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq258 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq266 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq263
    | (have j0 := eq263 X0 X1
       grind)
    | exact resolve eq263 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq263
  have eq452 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq266 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq266
    | exact resolve eq266 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq266 (σ X0) X1
       grind)
    | exact superpose eq266 eq15
    | (have j1 := eq266 (σ X0) X1
       grind)
    | exact resolve eq15 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq479 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq464
    | (have j0 := eq464 X0 X1
       grind)
    | exact resolve eq464 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq496 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq452 (τ X1) X0
       grind)
    | exact superpose eq452 eq18
    | (have j1 := eq452 (τ X1) X0
       grind)
    | exact resolve eq18 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq452
  have eq820 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq496 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq496
    | exact resolve eq496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq860 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq820 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq820
    | (have j0 := eq820 X0 X1
       grind)
    | exact resolve eq820 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq3613 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq479 x y
       grind)
    | exact superpose eq479 eq16
    | (have j1 := eq479 x y
       grind)
    | exact resolve eq16 eq479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3637 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq3671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3613
       have i₂ := eq860 y x
       grind)
    | exact superpose eq860 eq3613
    | (have j1 := eq860 y x
       grind)
    | (have r₁ := eq3613
       have r₂ := eq860 y x
       grind)
    | exact resolve eq3613 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613
  have eq3672 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3671
  have eq3698 : y ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3672
       grind)
    | exact superpose eq3672 eq12
    | exact resolve eq12 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3699 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq3672
       grind)
    | exact superpose eq3672 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3672
       grind)
    | exact resolve eq13 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3672
  have eq3707 : (k x y) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3699
  have eq3708 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq3698
       have r₂ := eq3707
       grind)
    | exact resolve eq3698 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3698 eq3707
  have eq3716 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq250 x y
       have i₂ := eq3708
       grind)
    | exact superpose eq3708 eq250
    | (have j0 := eq250 x y
       grind)
    | exact resolve eq250 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq3728 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3716
  have eq3729 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3728
  have eq3862 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3729
       grind)
    | exact superpose eq3729 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3729
       grind)
    | exact resolve eq12 eq3729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq3871 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3862
  have eq3879 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3871
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3871
    | exact resolve eq3871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq4118 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3879
       grind)
    | exact superpose eq3879 eq12
    | exact resolve eq12 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4119 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3879
       grind)
    | exact superpose eq3879 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq3879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3879
  have eq4127 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq4119
       have r₂ := eq66 x
       grind)
    | exact resolve eq4119 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4119
  have eq4128 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq4118
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4118
    | exact resolve eq4118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq4129 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq4127
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4127
    | exact resolve eq4127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127
  have eq4130 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq4129
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq4129
    | exact resolve eq4129 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq4131 : (σ y) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4130
       have r₂ := eq4128
       grind)
    | exact resolve eq4130 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128 eq4130
  have eq4266 : (σ y) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq4131
  have eq4465 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3637 x y
       have i₂ := eq3708
       grind)
    | exact superpose eq3708 eq3637
    | (have j0 := eq3637 x y
       grind)
    | exact resolve eq3637 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637 eq3708
  have eq4491 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4465
  have eq4492 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq4491
  have eq4574 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4492
       grind)
    | exact superpose eq4492 eq16
    | exact resolve eq16 eq4492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4578 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4492
       grind)
    | exact superpose eq4492 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq4492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq4586 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4578
       have r₂ := eq66 x
       grind)
    | exact resolve eq4578 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578
  have eq4588 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4586
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4586
    | exact resolve eq4586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4586
  have eq4589 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4588
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq4588
    | exact resolve eq4588 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq4588
  have eq4590 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4589
       have r₂ := eq4266
       grind)
    | exact resolve eq4589 eq4266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4266 eq4589
  have eq4725 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq860 y x
       have i₂ := eq4590
       grind)
    | exact superpose eq4590 eq860
    | (have j0 := eq860 y x
       grind)
    | exact resolve eq860 eq4590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq4590
  have eq4786 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq4725
       have r₂ := eq4574
       grind)
    | exact resolve eq4725 eq4574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4725
  have eq4936 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4574
       have i₂ := eq4786
       grind)
    | exact superpose eq4786 eq4574
    | exact resolve eq4574 eq4786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4574 eq4786
  have eq4951 : False := by grind
  exact eq4951

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_pyx_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
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
       have j1 := eq14 X1 X0
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
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq30 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 X0 X1
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq43 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq38
    | (have j0 := eq38 X0 X1
       grind)
    | exact resolve eq38 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq42 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq43 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq43
  have eq86 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       have j1 := eq45 X1 X0
       grind)
    | (have r₁ := eq86 X1 X0
       have r₂ := eq45 X0 X1
       grind)
    | (have r₁ := eq86 X0 X0
       have r₂ := eq45 X0 X0
       grind)
    | exact resolve eq86 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq86
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq90 (σ X1) (σ X0)
       grind)
    | exact superpose eq90 eq15
    | exact resolve eq15 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq90 X1 X0
       grind)
    | exact superpose eq90 eq193
    | exact resolve eq193 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq193
  have eq202 : False := by grind
  exact eq202

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  clear eq35
  have eq50 : y = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : y ≠ (M.op x y) ∨ (k x y) = (M.op y y) := by
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
  have eq63 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 ∨ (k X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = (M.op (M.op X0 (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
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
  have eq75 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq584
    | exact resolve eq584 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq585
       have r₂ := eq27
       grind)
    | exact resolve eq585 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq590 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq588
    | exact resolve eq588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq590
    | exact resolve eq590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq594 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq63
    | (have r₁ := eq63
       have r₂ := eq592
       grind)
    | exact resolve eq63 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq51
    | exact resolve eq51 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq27
    | exact resolve eq27 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq598 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq594
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq93 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq654 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq650 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq650 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq664 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq654 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq654
    | (have j0 := eq654 X0 X1
       grind)
    | exact resolve eq654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq674 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq598 eq117
    | exact resolve eq117 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598
  have eq677 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq674
  have eq714 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq595 eq14
    | exact resolve eq14 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq739 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq714 eq677
    | exact resolve eq677 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq714
  have eq745 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq739
  have eq749 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq745
       have r₂ := eq596
       grind)
    | exact resolve eq745 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq745
  have eq753 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq749 eq75
    | (have r₁ := eq75
       have r₂ := eq749
       grind)
    | exact resolve eq75 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq756 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq749 eq27
    | exact resolve eq27 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq753
  have eq763 : (M.op y (M.op y (M.op x y))) ≠ (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y)) ∨ (k (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y))) = (M.op (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y)) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y))) := by
    first
    | exact superpose eq50 eq64
    | exact resolve eq64 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq820 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq757 eq117
    | exact resolve eq117 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq824 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq820
  have eq831 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq824
       have r₂ := eq756
       grind)
    | exact resolve eq824 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq824
  have eq835 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq831 eq26
    | exact resolve eq26 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq831 eq117
    | exact resolve eq117 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq831
  have eq861 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq844
  have eq1041 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq835 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq835
       grind)
    | exact resolve eq13 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq1043 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1041
       have r₂ := eq749
       grind)
    | exact resolve eq1041 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq1041
  have eq1120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1043 eq861
    | exact resolve eq861 eq1043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq1043
  have eq1124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1120
  have eq1127 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1124
       have r₂ := eq27
       grind)
    | exact resolve eq1124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1129 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1127 eq20
    | exact resolve eq20 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : y = (M.op y (M.op y (M.op y y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1127 eq50
    | exact resolve eq50 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1132 : y ≠ y ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1127 eq62
    | (have r₁ := eq62
       have r₂ := eq1127
       grind)
    | exact resolve eq62 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1127
  have eq1142 : (k x y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1132
  have eq1152 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1129
    | exact resolve eq1129 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1203 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1152 eq26
    | exact resolve eq26 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1247 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1203 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1203
       grind)
    | exact resolve eq12 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1250 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1247
       have r₂ := eq27
       grind)
    | exact resolve eq1247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1310 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1142
       grind)
    | exact superpose eq1142 eq44
    | exact resolve eq44 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq2444 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq1131
       grind)
    | exact superpose eq1131 eq14
    | exact resolve eq14 eq1131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq2454 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1310
       have i₂ := eq2444
       grind)
    | exact superpose eq2444 eq1310
    | exact resolve eq1310 eq2444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310 eq2444
  have eq2461 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2454
  have eq2463 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2461
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2461
    | exact resolve eq2461 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq2470 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1152 eq2463
    | exact resolve eq2463 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2485 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2463 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2486 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2485
  have eq2500 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2470
  have eq2501 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2486
    | exact resolve eq2486 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486
  have eq2505 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2501
    | exact resolve eq2501 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq4518 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2505 eq27
    | exact resolve eq27 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq4530 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4518
       have r₂ := eq1152
       grind)
    | exact resolve eq4518 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152 eq4518
  have eq4534 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4530 eq27
    | exact resolve eq27 eq4530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4540 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4530 eq1250
    | (have r₁ := eq1250
       have r₂ := eq4530
       grind)
    | exact resolve eq1250 eq4530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq4530
  have eq4541 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4540
  have eq4542 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4541
  have eq4550 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4542 eq2500
    | exact resolve eq2500 eq4542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500 eq4542
  have eq4560 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4550
  have eq4565 : x = (M.op x y) := by
    first
    | (have r₁ := eq4560
       have r₂ := eq4534
       grind)
    | exact resolve eq4560 eq4534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4534 eq4560
  have eq4569 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4565 eq20
    | exact resolve eq20 eq4565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq4574 : x ≠ x ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq4565 eq74
    | (have r₁ := eq74
       have r₂ := eq4565
       grind)
    | exact resolve eq74 eq4565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4587 : x = (k x y) ∨ x = y := by grind
  clear eq4574
  have eq4601 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4569
    | exact resolve eq4569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4569
  have eq4604 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq4601 eq26
    | exact resolve eq26 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4671 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq4587
       grind)
    | exact superpose eq4587 eq44
    | exact resolve eq44 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq4678 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq652 x y
       have i₂ := eq4587
       grind)
    | exact superpose eq4587 eq652
    | (have j0 := eq652 x y
       grind)
    | exact resolve eq652 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq4587
  have eq4681 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4678
  have eq4690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4681
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4681
    | exact resolve eq4681 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4681
  have eq4693 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4601 eq4671
    | exact resolve eq4671 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4671
  have eq4695 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4690
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4690
    | exact resolve eq4690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4690
  have eq4698 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4693
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4693
    | exact resolve eq4693 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693
  have eq4699 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq4695
    | exact resolve eq4695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695
  have eq4702 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4601 eq4698
    | exact resolve eq4698 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4698
  have eq4703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4601 eq4699
    | exact resolve eq4699 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4699
  have eq4706 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq4703
       have r₂ := eq27
       grind)
    | exact resolve eq4703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4703
  have eq4709 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4706
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4706
    | exact resolve eq4706 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4706
  have eq4712 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4709
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4709
    | exact resolve eq4709 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709
  have eq4715 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq4712
    | exact resolve eq4712 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4712
  have eq4726 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq4715 eq27
    | exact resolve eq27 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4727 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ x = y := by
    first
    | exact superpose eq4715 eq51
    | exact resolve eq51 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4728 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4715 eq63
    | (have r₁ := eq63
       have r₂ := eq4715
       grind)
    | exact resolve eq63 eq4715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq4715
  have eq4735 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq4728
  have eq4736 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4601 eq4735
    | exact resolve eq4735 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq6275 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq4736 eq4702
    | exact resolve eq4702 eq4736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4702 eq4736
  have eq6285 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq6275
  have eq8099 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq4727 eq14
    | exact resolve eq14 eq4727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727
  have eq8111 : (M.op y (M.op y x)) ≠ (M.op (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) y)) ∨ (k (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y))) = (M.op (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y)) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) y))) := by
    first
    | exact superpose eq4565 eq763
    | exact resolve eq763 eq4565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq8112 : (k (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) y))) = (M.op (M.op (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) y)) (M.op (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) y))) ∨ (M.op y (M.op y x)) ≠ (M.op (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) y)) := by
    first
    | exact superpose eq4565 eq8111
    | exact resolve eq8111 eq4565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8111
  have eq8122 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq8099 eq6285
    | exact resolve eq6285 eq8099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6285 eq8099
  have eq8132 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq8122
  have eq8137 : x = y := by
    first
    | (have r₁ := eq8132
       have r₂ := eq4726
       grind)
    | exact resolve eq8132 eq4726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4726 eq8132
  have eq8139 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8137
       grind)
    | exact superpose eq8137 eq18
    | exact resolve eq18 eq8137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq8140 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8137
       grind)
    | exact superpose eq8137 eq24
    | exact resolve eq24 eq8137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8198 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8140
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8140
    | exact resolve eq8140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8140
  have eq8199 : x = (M.op x x) := by
    first
    | exact superpose eq4565 eq8139
    | exact resolve eq8139 eq4565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565 eq8139
  have eq8213 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4601 eq8198
    | exact resolve eq8198 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8216 : (k (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) = (M.op (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) ∨ (M.op y (M.op y x)) ≠ (M.op (M.op y (M.op y x)) (M.op (M.op y (M.op y x)) y)) := by
    first
    | (have i₁ := eq8112
       have i₂ := eq8137
       grind)
    | exact superpose eq8137 eq8112
    | exact resolve eq8112 eq8137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8112
  have eq8217 : (M.op x (M.op x x)) ≠ (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) ∨ (k (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) = (M.op (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) := by
    first
    | (have i₁ := eq8216
       have i₂ := eq8137
       grind)
    | exact superpose eq8137 eq8216
    | exact resolve eq8216 eq8137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8137 eq8216
  have eq8257 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8213 eq4604
    | exact resolve eq4604 eq8213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604 eq8213
  have eq8324 : (M.op x x) ≠ (M.op (M.op x x) (M.op (M.op x x) x)) ∨ (k (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) = (M.op (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) := by
    first
    | (have i₁ := eq8217
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8217
    | exact resolve eq8217 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8217
  have eq8325 : x ≠ (M.op x (M.op x x)) ∨ (k (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) = (M.op (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) := by
    first
    | (have i₁ := eq8324
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8324
    | exact resolve eq8324 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8324
  have eq8326 : x ≠ (M.op x x) ∨ (k (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) = (M.op (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) := by
    first
    | (have i₁ := eq8325
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8325
    | exact resolve eq8325 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8325
  have eq8327 : (k (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) = (M.op (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x)) (M.op (M.op x (M.op x x)) (M.op (M.op x (M.op x x)) x))) := by
    first
    | (have r₁ := eq8326
       have r₂ := eq8199
       grind)
    | exact resolve eq8326 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8326
  have eq8328 : (k (M.op x x) (M.op (M.op x x) (M.op (M.op x x) x))) = (M.op (M.op (M.op x x) (M.op (M.op x x) x)) (M.op (M.op x x) (M.op (M.op x x) x))) := by
    first
    | (have i₁ := eq8327
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8327
    | exact resolve eq8327 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8327
  have eq8329 : (k x (M.op x (M.op x x))) = (M.op (M.op x (M.op x x)) (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq8328
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8328
    | exact resolve eq8328 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8328
  have eq8330 : (k x (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq8329
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8329
    | exact resolve eq8329 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8329
  have eq8331 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq8330
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8330
    | exact resolve eq8330 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8330
  have eq8332 : x = (k x x) := by
    first
    | (have i₁ := eq8331
       have i₂ := eq8199
       grind)
    | exact superpose eq8199 eq8331
    | exact resolve eq8331 eq8199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8199 eq8331
  have eq8340 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq664 x x
       have i₂ := eq8332
       grind)
    | exact superpose eq8332 eq664
    | (have j0 := eq664 x x
       grind)
    | exact resolve eq664 eq8332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq8332
  have eq8345 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8340
  have eq8346 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq8345
  have eq8357 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8346
    | exact resolve eq8346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8346
  have eq8365 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4601 eq8357
    | exact resolve eq8357 eq4601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4601 eq8357
  have eq8373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8257 eq8365
    | exact resolve eq8365 eq8257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8257 eq8365
  have eq8381 : False := by grind
  exact eq8381

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  clear eq35
  have eq50 : y = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq101 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq98 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq101
    | exact resolve eq101 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq102
       have r₂ := eq27
       grind)
    | exact resolve eq102 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq105
    | exact resolve eq105 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq109 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107 eq27
    | exact resolve eq27 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y y) := by
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
  have eq111 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq127 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq65 sF3
       grind)
    | exact superpose eq65 eq123
    | exact resolve eq123 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq129 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq127
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq127
    | exact resolve eq127 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq127
  have eq256 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (σ y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107 eq51
    | exact resolve eq51 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq260 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq256 eq14
    | exact resolve eq14 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq297 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq260 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107 eq111
    | (have r₁ := eq111
       have r₂ := eq107
       grind)
    | exact resolve eq111 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq111
  have eq417 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq416
  have eq420 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq417 eq98
    | exact resolve eq98 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417
  have eq423 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq420
  have eq430 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq260 eq423
    | exact resolve eq423 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq423
  have eq451 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq430
  have eq454 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq451
       have r₂ := eq109
       grind)
    | exact resolve eq451 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq451
  have eq455 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq454 eq297
    | (have j0 := eq297 (σ x)
       grind)
    | (have r₁ := eq297 (σ x)
       have r₂ := eq454
       grind)
    | exact resolve eq297 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq454
  have eq458 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq455
  have eq459 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq458
  have eq462 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq459
    | exact resolve eq459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq462 eq98
    | exact resolve eq98 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq462
  have eq519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq516
  have eq523 : y = (M.op x y) := by
    first
    | (have r₁ := eq519
       have r₂ := eq27
       grind)
    | exact resolve eq519 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq525 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq523 eq20
    | exact resolve eq20 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq527 : y = (M.op y (M.op y (M.op y y))) := by
    first
    | exact superpose eq523 eq50
    | exact resolve eq50 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq528 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq523 eq110
    | (have r₁ := eq110
       have r₂ := eq523
       grind)
    | exact resolve eq110 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq533 : (M.op y x) = (M.op y y) ∨ (k x y) = (M.op y y) := by grind
  clear eq528
  have eq539 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq525
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq525
    | exact resolve eq525 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq542 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq539 eq26
    | exact resolve eq26 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq623 : y = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq527
       grind)
    | exact superpose eq527 eq14
    | exact resolve eq14 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq661 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq129
    | exact resolve eq129 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq681 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq539 eq661
    | exact resolve eq661 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq684 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq681
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq681
    | exact resolve eq681 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq686 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq539 eq684
    | exact resolve eq684 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq752 : y = (M.op y x) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq533
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq533
    | exact resolve eq533 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq753 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq752
       have i₂ := eq623
       grind)
    | exact superpose eq623 eq752
    | exact resolve eq752 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623 eq752
  have eq757 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq753
       grind)
    | exact superpose eq753 eq44
    | exact resolve eq44 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq753
  have eq764 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq539 eq757
    | exact resolve eq757 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq766 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq764
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq764
    | exact resolve eq764 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq767 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq539 eq766
    | exact resolve eq766 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq770 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq767 eq76
    | (have j0 := eq76 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq76 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq767
  have eq771 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq770
  have eq773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq542 eq771
    | exact resolve eq771 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq776 : y = (M.op y x) := by
    first
    | (have r₁ := eq773
       have r₂ := eq27
       grind)
    | exact resolve eq773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq787 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq776
       grind)
    | exact superpose eq776 eq14
    | exact resolve eq14 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq790 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq787
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq787
    | exact resolve eq787 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq795 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq523 eq790
    | exact resolve eq790 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq800 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq795
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq795
    | exact resolve eq795 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq803 : x = (M.op x y) := by
    first
    | exact superpose eq523 eq800
    | exact resolve eq800 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq806 : x = (M.op x y) := by
    first
    | (have i₁ := eq803
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq803
    | exact resolve eq803 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq803
  have eq809 : x = y := by
    first
    | exact superpose eq523 eq806
    | exact resolve eq806 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq806
  have eq816 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq809
       grind)
    | exact superpose eq809 eq24
    | exact resolve eq24 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq809
  have eq852 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq539 eq816
    | exact resolve eq816 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq816
  have eq862 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq852
    | exact resolve eq852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq852
  have eq900 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq862 eq542
    | exact resolve eq542 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq862
  have eq902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq686 eq900
    | exact resolve eq900 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq900
  have eq914 : False := by grind
  exact eq914

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq766 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq731 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq731
    | (have j0 := eq731 X0 X1
       grind)
    | exact resolve eq731 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq731
  have eq4890 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq766 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq766
    | exact resolve eq766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq4942 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4890 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq4890
    | (have j0 := eq4890 X0 X1
       grind)
    | exact resolve eq4890 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4890
  have eq4963 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4942 X0 X1
       have j1 := eq93 X1 X0
       grind)
    | (have r₁ := eq4942 X1 X0
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq4942 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq4942
  have eq4966 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4963 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4963
    | exact resolve eq4963 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4985 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4963 (σ y) x
       grind)
    | exact superpose eq4963 eq16
    | (have j1 := eq4963 (σ y) x
       grind)
    | exact resolve eq16 eq4963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq5057 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq4985
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4985
    | exact resolve eq4985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4985
  have eq5110 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4966 X0 X1
       grind)
    | exact superpose eq4966 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq4966 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq4966 X0 X1
       grind)
    | exact resolve eq13 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq4966 X0 X1
       grind)
    | exact superpose eq4966 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq4966 X0 X1
       grind)
    | exact resolve eq12 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5160 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq5110 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5110
  have eq5194 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5160 X0 X1
       have j1 := eq5111 X0 X1
       grind)
    | (have r₁ := eq5160 X0 X1
       have r₂ := eq5111 X0 X1
       grind)
    | exact resolve eq5160 eq5111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111 eq5160
  have eq5300 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq5194 X0 (σ X1)
       grind)
    | exact superpose eq5194 eq28
    | (have j1 := eq5194 X0 (σ X1)
       grind)
    | exact resolve eq28 eq5194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq5364 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5194 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5677 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq5300 (σ X0) X1
       grind)
    | exact superpose eq5300 eq22
    | (have j1 := eq5300 (σ X0) X1
       grind)
    | exact resolve eq22 eq5300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5300
  have eq5726 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5677 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq5677
    | (have j0 := eq5677 X0 X1
       grind)
    | exact resolve eq5677 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5677
  have eq5760 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5726 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5726
    | (have j0 := eq5726 X0 X1
       grind)
    | exact resolve eq5726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5726
  have eq5770 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5760 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5760
    | (have j0 := eq5760 X0 X1
       grind)
    | exact resolve eq5760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5760
  have eq5973 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq5770 X1 X0
       grind)
    | exact superpose eq5770 eq11
    | (have j1 := eq5770 X1 X0
       grind)
    | exact resolve eq11 eq5770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq6096 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5973 y x
       grind)
    | exact superpose eq5973 eq16
    | (have j1 := eq5973 y x
       grind)
    | exact resolve eq16 eq5973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973
  have eq6177 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq6096
       have i₂ := eq5194 x y
       grind)
    | exact superpose eq5194 eq6096
    | (have j1 := eq5194 x y
       grind)
    | exact resolve eq6096 eq5194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194 eq6096
  have eq6181 : x = (M.op x y) ∨ x = (k y x) := by grind
  clear eq6177
  have eq6182 : x = (k y x) := by
    first
    | (have j1 := eq5364 y x
       grind)
    | (have r₁ := eq6181
       have r₂ := eq5364 y x
       grind)
    | exact resolve eq6181 eq5364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5364 eq6181
  have eq8224 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq5057
       have i₂ := eq4966 x y
       grind)
    | exact superpose eq4966 eq5057
    | (have j1 := eq4966 x y
       grind)
    | exact resolve eq5057 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8225 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq8224
  have eq8228 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8225
       have i₂ := eq6182
       grind)
    | exact superpose eq6182 eq8225
    | exact resolve eq8225 eq6182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8225
  have eq8232 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8228
       have i₂ := eq6182
       grind)
    | exact superpose eq6182 eq8228
    | exact resolve eq8228 eq6182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8228
  have eq8234 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5057
       have i₂ := eq8232
       grind)
    | exact superpose eq8232 eq5057
    | exact resolve eq5057 eq8232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5057 eq8232
  have eq8248 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8234
  have eq8249 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8248
       have i₂ := eq6182
       grind)
    | exact superpose eq6182 eq8248
    | exact resolve eq8248 eq6182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8248
  have eq8250 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8249
  have eq8254 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8250
       grind)
    | exact superpose eq8250 eq16
    | exact resolve eq16 eq8250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8250
  have eq8292 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq8254
       have i₂ := eq4966 x y
       grind)
    | exact superpose eq4966 eq8254
    | (have j1 := eq4966 x y
       grind)
    | exact resolve eq8254 eq4966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4966
  have eq8293 : (M.op x y) = (k y x) := by grind
  clear eq8292
  have eq8297 : x = (M.op x y) := by
    first
    | (have i₁ := eq8293
       have i₂ := eq6182
       grind)
    | exact superpose eq6182 eq8293
    | exact resolve eq8293 eq6182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6182 eq8293
  have eq8301 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq8254
       have i₂ := eq8297
       grind)
    | exact superpose eq8297 eq8254
    | exact resolve eq8254 eq8297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8254 eq8297
  have eq8314 : False := by grind
  exact eq8314

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq37 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq31 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq31 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq36 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq40
    | (have j0 := eq40 X0 X1
       grind)
    | exact resolve eq40 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq37 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq37 X0 X1
       grind)
    | (have r₁ := eq42 X0 (M.op X1 X1)
       have r₂ := eq37 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq37 (k X1 X1) X1
       grind)
    | exact resolve eq42 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq42
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq44 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq44 X0 X1
       grind)
    | exact resolve eq45 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq45
  have eq106 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq106 X1 X0
       have r₂ := eq48 X0 X1
       grind)
    | (have r₁ := eq106 X0 X0
       have r₂ := eq48 X0 X0
       grind)
    | exact resolve eq106 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq106
  have eq225 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq110 (σ X1) (σ X0)
       grind)
    | exact superpose eq110 eq15
    | exact resolve eq15 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq225 X0 X1
       have i₂ := eq110 X1 X0
       grind)
    | exact superpose eq110 eq225
    | exact resolve eq225 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq225
  have eq232 : False := by grind
  exact eq232

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq143 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq885 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq143 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq143
    | (have j0 := eq143 (σ X1) (σ X0)
       grind)
    | exact resolve eq143 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq4179 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq84 X1 X0
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq84 X0 (σ X0)
       grind)
    | (have r₁ := eq13 (M.op (σ X0) (σ X0)) X1
       have r₂ := eq84 X0 (M.op X1 (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4201 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq4202 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4201 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4201
  have eq4204 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4179 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4179
  have eq4205 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4209 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4202 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4202
    | (have j0 := eq4202 X0
       grind)
    | exact resolve eq4202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4250 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4209 X0
       grind)
    | exact superpose eq4209 eq38
    | (have j1 := eq4209 X0
       grind)
    | exact resolve eq38 eq4209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq4209
  have eq4261 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4250 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4250
    | (have j0 := eq4250 X0
       grind)
    | exact resolve eq4250 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4250
  have eq4262 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4261 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4261
  have eq4265 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4262 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4262
    | exact resolve eq4262 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4288 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4262 X0
       grind)
    | exact superpose eq4262 eq11
    | exact resolve eq11 eq4262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262
  have eq4349 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4265 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq4265
    | exact resolve eq4265 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4265
  have eq4453 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4349 X0
       grind)
    | exact superpose eq4349 eq11
    | exact resolve eq11 eq4349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4349
  have eq4564 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4453 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4453
    | exact resolve eq4453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq5244 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5262 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5244 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5244
    | exact resolve eq5244 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5244
  have eq5293 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5262 X0
       have i₂ := eq4564 X0
       grind)
    | exact superpose eq4564 eq5262
    | exact resolve eq5262 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5262
  have eq5309 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5293
  have eq25750 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq885 (τ X0) (τ X1)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq885
    | (have j0 := eq885 (τ X0) (τ X1)
       grind)
    | exact resolve eq885 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq885
  have eq25828 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25750 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq25750
    | (have j0 := eq25750 X0 X1
       grind)
    | exact resolve eq25750 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25750
  have eq25883 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25828 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25828
    | (have j0 := eq25828 X0 X1
       grind)
    | exact resolve eq25828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25828
  have eq25937 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25883 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25883
    | (have j0 := eq25883 X0 X1
       grind)
    | exact resolve eq25883 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25883
  have eq25987 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25937 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25937
    | (have j0 := eq25937 X0 X1
       grind)
    | exact resolve eq25937 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25937
  have eq26029 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) (σ (τ X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25987 X0 X1
       have i₂ := eq4288 (σ (τ X1))
       grind)
    | exact superpose eq4288 eq25987
    | (have j0 := eq25987 X0 X1
       grind)
    | exact resolve eq25987 eq4288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25987
  have eq26069 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (k (τ X1) (τ X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26029 X0 X1
       have i₂ := eq15 (τ X1) (τ X1)
       grind)
    | exact superpose eq15 eq26029
    | (have j0 := eq26029 X0 X1
       grind)
    | exact resolve eq26029 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26029
  have eq26106 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k (σ (τ X1)) X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26069 X0 X1
       have i₂ := eq19 X1 (τ X1)
       grind)
    | exact superpose eq19 eq26069
    | (have j0 := eq26069 X0 X1
       grind)
    | exact resolve eq26069 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26069
  have eq26141 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26106 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq26106
    | (have j0 := eq26106 X0 X1
       grind)
    | exact resolve eq26106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26106
  have eq26168 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26141 X0 X1
       have i₂ := eq4564 X1
       grind)
    | exact superpose eq4564 eq26141
    | (have j0 := eq26141 X0 X1
       grind)
    | exact resolve eq26141 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26141
  have eq26191 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26168 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26168
    | (have j0 := eq26168 X0 X1
       grind)
    | exact resolve eq26168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26168
  have eq32179 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq4205 (σ X0) X1
       grind)
    | exact superpose eq4205 eq30
    | (have j1 := eq4205 (σ X0) X1
       grind)
    | exact resolve eq30 eq4205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4205
  have eq32286 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32179 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq32179
    | (have j0 := eq32179 X0 X1
       grind)
    | exact resolve eq32179 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32179
  have eq32384 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32286 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32286
    | (have j0 := eq32286 X0 X1
       grind)
    | exact resolve eq32286 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32286
  have eq32477 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32384 X0 X1
       have i₂ := eq4288 X1
       grind)
    | exact superpose eq4288 eq32384
    | (have j0 := eq32384 X0 X1
       grind)
    | exact resolve eq32384 eq4288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288 eq32384
  have eq32553 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq32477 X0 X1
       have i₂ := eq4564 X1
       grind)
    | exact superpose eq4564 eq32477
    | (have j0 := eq32477 X0 X1
       grind)
    | exact resolve eq32477 eq4564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4564 eq32477
  have eq32604 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32553 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq32553
    | (have j0 := eq32553 X0 X1
       grind)
    | exact resolve eq32553 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32553
  have eq34920 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq32604 X0 X1
       grind)
    | exact superpose eq32604 eq11
    | (have j1 := eq32604 X0 X1
       grind)
    | exact resolve eq11 eq32604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32604
  have eq35400 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34920 y x
       grind)
    | exact superpose eq34920 eq16
    | (have j1 := eq34920 y x
       grind)
    | exact resolve eq16 eq34920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34920
  have eq36299 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq35400
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq35400
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq35400 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35400
  have eq36302 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq36299
  have eq36303 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq36302
  have eq36307 : y ≠ y ∨ y = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq36303
       grind)
    | exact superpose eq36303 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq36303
       grind)
    | exact resolve eq13 eq36303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36314 : y ≠ y ∨ y = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq36307
  have eq36315 : y = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq36314
  have eq36800 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq26191 y x
       have i₂ := eq36315
       grind)
    | exact superpose eq36315 eq26191
    | (have j0 := eq26191 y x
       grind)
    | exact resolve eq26191 eq36315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26191 eq36315
  have eq36805 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq36800
  have eq36806 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq36805
  have eq36827 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq36806
       grind)
    | exact superpose eq36806 eq16
    | exact resolve eq16 eq36806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36806
  have eq37264 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq36827
       have i₂ := eq36303
       grind)
    | exact superpose eq36303 eq36827
    | exact resolve eq36827 eq36303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36303 eq36827
  have eq37265 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq37264
  have eq37266 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq37265
  have eq37278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5309 x
       have i₂ := eq37266
       grind)
    | exact superpose eq37266 eq5309
    | exact resolve eq5309 eq37266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37266
  have eq37299 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq37278
       have r₂ := eq16
       grind)
    | exact resolve eq37278 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37278
  have eq37687 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq37299
       grind)
    | exact superpose eq37299 eq10
    | exact resolve eq10 eq37299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37299
  have eq37818 : y = (M.op x x) := by
    first
    | (have i₁ := eq37687
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq37687
    | exact resolve eq37687 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37687
  have eq37919 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5309 x
       have i₂ := eq37818
       grind)
    | exact superpose eq37818 eq5309
    | exact resolve eq5309 eq37818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309 eq37818
  have eq37941 : False := by grind
  exact eq37941
