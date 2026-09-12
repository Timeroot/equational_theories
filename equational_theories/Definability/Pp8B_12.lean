import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1489 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1489 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq289 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq292 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq290 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq290 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq290 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq292 (σ X0)
       grind)
    | exact superpose eq292 eq15
    | exact resolve eq15 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq303
    | exact resolve eq303 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292 eq303
  have eq368 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq322 X0
       grind)
    | exact superpose eq322 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq372 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq368 X0 X1
       have j1 := eq370 X0 X1
       grind)
    | (have r₁ := eq368 X0 X1
       have r₂ := eq370 X0 X1
       grind)
    | exact resolve eq368 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq370
  have eq480 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq372 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq372
    | exact resolve eq372 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq372 X1 (σ X0)
       grind)
    | exact superpose eq372 eq15
    | (have j1 := eq372 X1 (σ X0)
       grind)
    | exact resolve eq15 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq537 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq480 X1 (τ X0)
       grind)
    | exact superpose eq480 eq17
    | (have j1 := eq480 X1 (τ X0)
       grind)
    | exact resolve eq17 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq480
  have eq650 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq537 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq537
    | exact resolve eq537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq537 X1 X0
       grind)
    | exact superpose eq537 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq537 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq537 X0 X1
       grind)
    | exact resolve eq13 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq683 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq666 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq700 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq1004 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq493 x y
       grind)
    | exact superpose eq493 eq16
    | (have j1 := eq493 x y
       grind)
    | exact resolve eq16 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq95633 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq683
    | (have j0 := eq683 X1 X1
       grind)
    | exact resolve eq683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq95918 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95633 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq95633
    | (have j0 := eq95633 X0 X1
       grind)
    | exact resolve eq95633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95633
  have eq96278 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq95918 X0 X1
       grind)
    | exact superpose eq95918 eq10
    | (have j1 := eq95918 X0 X1
       grind)
    | exact resolve eq10 eq95918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95918
  have eq96417 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq96278 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq96278
    | (have j0 := eq96278 X0 X1
       grind)
    | exact resolve eq96278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96278
  have eq96486 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq96417 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq96417 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq96417 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96417
  have eq97643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1004
       have i₂ := eq96486 x y
       grind)
    | exact superpose eq96486 eq1004
    | (have j1 := eq96486 x y
       grind)
    | exact resolve eq1004 eq96486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq97644 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq96486 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96486
  have eq97645 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq97643
  have eq98226 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1025 x y
       have i₂ := eq97645
       grind)
    | exact superpose eq97645 eq1025
    | (have j0 := eq1025 x y
       grind)
    | exact resolve eq1025 eq97645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq97645
  have eq98257 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq98226
  have eq98258 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq98257
  have eq98266 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq98258
       grind)
    | exact superpose eq98258 eq16
    | exact resolve eq16 eq98258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98291 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq97644 (σ x) (σ y)
       have i₂ := eq98258
       grind)
    | exact superpose eq98258 eq97644
    | (have j0 := eq97644 (σ x) (σ y)
       grind)
    | (have r₁ := eq97644 (σ x) (σ y)
       have r₂ := eq98258
       grind)
    | exact resolve eq97644 eq98258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97644 eq98258
  have eq98292 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq98291
  have eq98294 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq98292
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq98292
    | exact resolve eq98292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98292
  have eq98328 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq700 x y
       have i₂ := eq98294
       grind)
    | exact superpose eq98294 eq700
    | (have j0 := eq700 x y
       grind)
    | exact resolve eq700 eq98294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700 eq98294
  have eq98489 : y = (M.op x y) := by
    first
    | (have r₁ := eq98328
       have r₂ := eq98266
       grind)
    | exact resolve eq98328 eq98266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98328
  have eq98592 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq98266
       have i₂ := eq98489
       grind)
    | exact superpose eq98489 eq98266
    | exact resolve eq98266 eq98489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98266 eq98489
  have eq98621 : False := by grind
  exact eq98621

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_pxy_y_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
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
  clear eq36
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
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
  have eq174 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq16 X0 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq174 (M.op y y)
       have i₂ := eq16 y y y
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 (M.op x y)) (M.op (M.op X0 (M.op y X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq175 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq196 : ∀ X1 : G, (M.op y (M.op X1 (M.op (M.op y (M.op x y)) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 (M.op X2 X0)
       have i₂ := eq180 X0 X2
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (k X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq209 X0 X1 X2
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq209
    | exact resolve eq209 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq378 : ∀ X0 : G, (k (σ X0) (k (σ x) (σ x))) = (σ (k X0 (k x x))) := by
    intro X0
    first
    | exact superpose eq97 eq38
    | exact resolve eq38 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq97
  have eq569 : (M.op y (M.op (M.op x y) y)) = (k y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq181 y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : y = (M.op (M.op x y) (k y (M.op y y))) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq174
    | exact resolve eq174 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (k X0 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180 (M.op X0 X0) X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq180
    | exact resolve eq180 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : y = (M.op (M.op x y) (k y (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq571
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq571
    | exact resolve eq571 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq585 : ∀ X0 : G, (M.op y (M.op X0 (M.op (k y (M.op (M.op x y) y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq579 eq16
    | exact resolve eq16 eq579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq587 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq196 sF0
       have i₂ := eq180 sF0 y
       grind)
    | exact superpose eq180 eq196
    | exact resolve eq196 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq597 : (M.op x y) = (M.op y (k (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq587
       have i₂ := eq181 sF0
       grind)
    | exact superpose eq181 eq587
    | exact resolve eq587 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq603 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq198 sF4
       have i₂ := eq180 sF4 sF3
       grind)
    | exact superpose eq180 eq198
    | exact resolve eq198 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq613 : (M.op (σ x) (σ y)) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq603
       have i₂ := eq181 sF4
       grind)
    | exact superpose eq181 eq603
    | exact resolve eq603 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq637 : ∀ X0 : G, y = (M.op (M.op X0 y) (k y (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq570 y X0
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq570
    | exact resolve eq570 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq11
    | exact resolve eq11 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq181 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq755 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq767 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq775 : ∀ X0 : G, (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq715 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq777 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq702
  have eq795 : (M.op x y) = (k y x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq739
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq739
    | exact resolve eq739 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq835 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq768 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq768
    | (have j0 := eq768 (σ X0)
       grind)
    | exact resolve eq768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : (M.op y y) = (M.op (k y y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq777 eq180
    | exact resolve eq180 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : (M.op (M.op x y) y) = (M.op (k y y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq917
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq917
    | exact resolve eq917 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq927 : (k y y) = (M.op (k y y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq777 eq921
    | exact resolve eq921 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq921
  have eq963 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 X0 (M.op X0 X1)
       have i₂ := eq180 (M.op X0 X1) X1
       grind)
    | exact superpose eq180 eq176
    | exact resolve eq176 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq988 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 X1
       have i₂ := eq181 (M.op X0 X1)
       grind)
    | exact superpose eq181 eq963
    | exact resolve eq963 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1062 : ∀ X0 : G, (M.op (k X0 (M.op X0 X0)) (k X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq213 X0 X0 X0
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq213
    | exact resolve eq213 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1073 : y = (M.op (k y (M.op (M.op x y) y)) (k y (M.op y y))) := by
    first
    | exact superpose eq569 eq213
    | exact resolve eq213 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 y)) (k y (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq213 y X0 X1
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq213
    | exact resolve eq213 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1095 : y = (M.op (k y (M.op (M.op x y) y)) (k y (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq1073
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq1073
    | exact resolve eq1073 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1636 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq795
       grind)
    | exact superpose eq795 eq39
    | exact resolve eq39 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1637 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1636
    | exact resolve eq1636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1639 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1637
    | exact resolve eq1637 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq2463 : ∀ X0 : G, (M.op (k X0 (M.op X0 X0)) X0) = (k (k X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq181 (k X0 (M.op X0 X0))
       have i₂ := eq1062 X0
       grind)
    | exact superpose eq1062 eq181
    | exact resolve eq181 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2470 : ∀ X0 : G, (M.op X0 (k X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq180 (k X0 (M.op X0 X0)) (k X0 (M.op X0 X0))
       have i₂ := eq1062 X0
       grind)
    | exact superpose eq1062 eq180
    | exact resolve eq180 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2478 : ∀ X0 : G, (M.op X0 (k X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2470 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq2470
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq2470 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2482 : y = (M.op y (k y (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq2470 y
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq2470
    | exact resolve eq2470 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2501 : ∀ X0 : G, (M.op X0 (k X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2478 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478
  have eq16784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1639 eq755
    | exact resolve eq755 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq16794 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq16784
       have r₂ := eq27
       grind)
    | exact resolve eq16784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16784
  have eq16805 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16794 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16794
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16794
       grind)
    | exact resolve eq12 eq16794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16794
  have eq16822 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by grind
  clear eq16805
  have eq16823 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by grind
  clear eq16822
  have eq16831 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1639 eq16823
    | exact resolve eq16823 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639 eq16823
  have eq16858 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq16831 eq180
    | exact resolve eq180 eq16831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16831
  have eq16871 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16858
    | exact resolve eq16858 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858
  have eq16889 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq16871
       grind)
    | exact superpose eq16871 eq174
    | exact resolve eq174 eq16871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16899 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x y
       have i₂ := eq16871
       grind)
    | exact superpose eq16871 eq180
    | exact resolve eq180 eq16871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16915 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16871 eq16899
    | exact resolve eq16899 eq16871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16871 eq16899
  have eq16922 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16889
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16889
    | exact resolve eq16889 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16889
  have eq16931 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq16915
       grind)
    | exact superpose eq16915 eq181
    | exact resolve eq181 eq16915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16947 : x = (M.op y (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq570 x x
       have i₂ := eq16915
       grind)
    | exact superpose eq16915 eq570
    | exact resolve eq570 eq16915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16915
  have eq16962 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16931
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16931
    | exact resolve eq16931 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16931
  have eq17001 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16922 eq180
    | exact resolve eq180 eq16922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16922
  have eq17079 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17001 eq180
    | exact resolve eq180 eq17001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17092 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17079
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq17079
    | exact resolve eq17079 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17079
  have eq17101 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17092
    | exact resolve eq17092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17092
  have eq17139 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17101 eq17001
    | exact resolve eq17001 eq17101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17001 eq17101
  have eq17161 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17139
  have eq17182 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17161 eq180
    | exact resolve eq180 eq17161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17193 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17161 eq17182
    | exact resolve eq17182 eq17161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17161 eq17182
  have eq17201 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17193 eq181
    | exact resolve eq181 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17206 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17193 eq1062
    | exact resolve eq1062 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq17582 : ∀ X0 : G, (M.op (k (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op (M.op (k (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (k (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq597 eq183
    | exact resolve eq183 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq597
  have eq17668 : ∀ X0 : G, (M.op (k (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq17582 X0
       have i₂ := eq570 sF0 (k sF0 (M.op sF0 sF0))
       grind)
    | exact superpose eq570 eq17582
    | exact resolve eq17582 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17582
  have eq17688 : (M.op (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq17668 x
       have i₂ := eq180 sF0 x
       grind)
    | exact superpose eq180 eq17668
    | exact resolve eq17668 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17668
  have eq17691 : (M.op (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq17688
       have i₂ := eq2463 sF0
       grind)
    | exact superpose eq2463 eq17688
    | exact resolve eq17688 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463 eq17688
  have eq17930 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16947
       have i₂ := eq16962
       grind)
    | exact superpose eq16962 eq16947
    | exact resolve eq16947 eq16962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16947 eq16962
  have eq17951 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17930
  have eq18029 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17951 eq180
    | exact resolve eq180 eq17951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18044 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18029
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq18029
    | exact resolve eq18029 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18029
  have eq18053 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18044
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18044
    | exact resolve eq18044 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18044
  have eq18074 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18053 eq17951
    | exact resolve eq17951 eq18053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17951 eq18053
  have eq18098 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18074
  have eq18113 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18098 eq177
    | exact resolve eq177 eq18098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18098
  have eq18152 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18113 x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq18113
    | exact resolve eq18113 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18113
  have eq18164 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq181 x
       have i₂ := eq18152
       grind)
    | exact superpose eq18152 eq181
    | exact resolve eq181 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18170 : x = (M.op x (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2470 x
       have i₂ := eq18152
       grind)
    | exact superpose eq18152 eq2470
    | exact resolve eq2470 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18171 : y = (k x x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq18152
       grind)
    | exact superpose eq18152 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18187 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18171
  have eq18195 : (M.op x y) = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18164
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18164
    | exact resolve eq18164 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18164
  have eq18255 : x = (k (k (M.op x y) x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17193 eq17691
    | exact resolve eq17691 eq17193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17193 eq17691
  have eq18269 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq18195
       grind)
    | exact superpose eq18195 eq40
    | exact resolve eq40 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq18275 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18269
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18269
    | exact resolve eq18269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18269
  have eq18279 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18275
    | exact resolve eq18275 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18275
  have eq18375 : x ≠ x ∨ (k x y) = (M.op x x) ∨ (k x y) = (k x (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x (k x y)
       have i₂ := eq18170
       grind)
    | exact superpose eq18170 eq12
    | (have j0 := eq12 x (k x y)
       grind)
    | (have r₁ := eq12 x (k x y)
       have r₂ := eq18170
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq18170
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18170
       grind)
    | exact resolve eq12 eq18170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18170
  have eq18391 : (k x y) = (M.op x x) ∨ (k x y) = (k x (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18375
  have eq18407 : y = (k x y) ∨ (k x y) = (k x (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18152 eq18391
    | exact resolve eq18391 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18391
  have eq18419 : y = (M.op x y) ∨ (k x y) = (k x (k x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18195 eq18407
    | exact resolve eq18407 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18407
  have eq18427 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18195 eq18419
    | exact resolve eq18419 eq18195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18195 eq18419
  have eq18662 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq18187
       grind)
    | exact superpose eq18187 eq39
    | exact resolve eq39 eq18187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18187
  have eq18677 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18662
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18662
    | exact resolve eq18662 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18662
  have eq18682 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18677
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18677
    | exact resolve eq18677 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18677
  have eq18703 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18682 eq775
    | (have j0 := eq775 (σ x)
       grind)
    | exact resolve eq775 eq18682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq18716 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18703
    | exact resolve eq18703 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18703
  have eq18722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18279 eq18716
    | exact resolve eq18716 eq18279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18279 eq18716
  have eq18725 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18722
       have r₂ := eq27
       grind)
    | exact resolve eq18722 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18722
  have eq18760 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18725 eq570
    | exact resolve eq570 eq18725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18725
  have eq18771 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18682 eq18760
    | exact resolve eq18760 eq18682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18682 eq18760
  have eq18785 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq18771
    | exact resolve eq18771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18771
  have eq18786 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq18785
  have eq18984 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18786 eq189
    | exact resolve eq189 eq18786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19000 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18984
    | exact resolve eq18984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18984
  have eq19002 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18786 eq19000
    | exact resolve eq19000 eq18786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19000
  have eq19020 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19002 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq19002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19002
  have eq19036 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq19020
  have eq19214 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19036 eq115
    | exact resolve eq115 eq19036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19036
  have eq19230 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19214
    | exact resolve eq19214 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19214
  have eq19240 : x = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq927
       have i₂ := eq19230
       grind)
    | exact superpose eq19230 eq927
    | exact resolve eq927 eq19230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq19263 : x = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19240
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19240
    | exact resolve eq19240 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19240
  have eq19264 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq19263
  have eq19296 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19264 eq186
    | exact resolve eq186 eq19264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq19332 : y = (k y (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19296
       have i₂ := eq181 y
       grind)
    | exact superpose eq181 eq19296
    | exact resolve eq19296 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19296
  have eq19354 : y = (k y (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19332
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq19332
    | exact resolve eq19332 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19332
  have eq19363 : y = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19264 eq19354
    | exact resolve eq19354 eq19264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19264 eq19354
  have eq19368 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19230 eq19363
    | exact resolve eq19363 eq19230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19230 eq19363
  have eq19369 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq19368
  have eq19374 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19369 eq31
    | exact resolve eq31 eq19369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq19524 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq19374
    | exact resolve eq19374 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19374
  have eq19525 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19524
  have eq19533 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19525 eq28
    | exact resolve eq28 eq19525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19624 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq19533
    | exact resolve eq19533 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19533
  have eq19625 : x = (M.op x y) ∨ x = y := by grind
  clear eq19624
  have eq21077 : (k (M.op x y) x) = (M.op x (k (k (M.op x y) x) (M.op (k (M.op x y) x) (k (M.op x y) x)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17201 eq988
    | exact resolve eq988 eq17201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17201
  have eq21189 : (k (M.op x y) x) = (M.op x (k (k (M.op x y) x) (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17206 eq21077
    | exact resolve eq21077 eq17206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17206 eq21077
  have eq21248 : (k (M.op x y) x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18255 eq21189
    | exact resolve eq21189 eq18255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21189
  have eq21267 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18152 eq21248
    | exact resolve eq21248 eq18152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18152 eq21248
  have eq21269 : x = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18786 eq21267
    | exact resolve eq21267 eq18786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18786 eq21267
  have eq21618 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21269 eq18255
    | exact resolve eq18255 eq21269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18255 eq21269
  have eq21627 : x = (k x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21618
  have eq21641 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21627 eq18427
    | exact resolve eq18427 eq21627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18427 eq21627
  have eq21651 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21641
  have eq21658 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19625 eq21651
    | exact resolve eq21651 eq19625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19625 eq21651
  have eq21659 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq21658
  have eq21665 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21659 eq178
    | exact resolve eq178 eq21659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq21666 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21659 eq189
    | exact resolve eq189 eq21659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq21674 : (σ x) = (M.op (σ y) (k (σ x) (M.op (σ x) (σ x)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21659 eq613
    | exact resolve eq613 eq21659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq21682 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq21666
    | exact resolve eq21666 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21666
  have eq21684 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21659 eq21682
    | exact resolve eq21682 eq21659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21659 eq21682
  have eq21695 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21684 eq181
    | exact resolve eq181 eq21684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21704 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21684 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq21684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21713 : (σ y) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21684 eq570
    | exact resolve eq570 eq21684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21722 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq21704
  have eq21980 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21722 eq115
    | exact resolve eq115 eq21722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq21722
  have eq22002 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq21980
    | exact resolve eq21980 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21980
  have eq22007 : x = (k x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19369 eq22002
    | exact resolve eq22002 eq19369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19369 eq22002
  have eq22021 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq22007
       grind)
    | exact superpose eq22007 eq39
    | exact resolve eq39 eq22007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq22023 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq835 x
       have i₂ := eq22007
       grind)
    | exact superpose eq22007 eq835
    | (have j0 := eq835 x
       grind)
    | exact resolve eq835 eq22007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq22007
  have eq22032 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22023
  have eq22041 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22032
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22032
    | exact resolve eq22032 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22032
  have eq22043 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22021
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22021
    | exact resolve eq22021 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22021
  have eq23707 : (σ x) = (M.op (σ y) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22041 eq21674
    | exact resolve eq21674 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21674
  have eq23737 : (σ x) = (M.op (σ y) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq23707
  have eq23753 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22043 eq23737
    | exact resolve eq23737 eq22043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22043 eq23737
  have eq23789 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23753 eq21665
    | exact resolve eq21665 eq23753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23753
  have eq23812 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq23789
  have eq23833 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22041 eq23812
    | exact resolve eq23812 eq22041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22041 eq23812
  have eq23834 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq23833
  have eq23932 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23834 eq21665
    | exact resolve eq21665 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21665
  have eq23935 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23834 eq21684
    | exact resolve eq21684 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21684
  have eq23936 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23834 eq21695
    | exact resolve eq21695 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21695
  have eq23938 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23834 eq21713
    | exact resolve eq21713 eq23834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21713 eq23834
  have eq23939 : (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq23938
  have eq23941 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq23936
  have eq23942 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq23935
  have eq23945 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23932 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23932
  have eq23963 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23941 eq23945
    | exact resolve eq23945 eq23941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23945
  have eq24050 : (M.op (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23942 eq573
    | exact resolve eq573 eq23942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq23942
  have eq24085 : (k (σ x) (σ x)) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23941 eq24050
    | exact resolve eq24050 eq23941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23941 eq24050
  have eq24109 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (k (σ x) (σ x)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23939 eq16
    | exact resolve eq16 eq23939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23939
  have eq24140 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op X0 (σ x)) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24085 eq24109
    | exact resolve eq24109 eq24085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24085 eq24109
  have eq24147 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23963 eq24140
    | exact resolve eq24140 eq23963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23963 eq24140
  have eq24161 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24147 eq141
    | exact resolve eq141 eq24147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq24147
  have eq24177 : x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq24161
    | exact resolve eq24161 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24161
  have eq24198 : x ≠ x ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq768 x
       have i₂ := eq24177
       grind)
    | exact superpose eq24177 eq768
    | (have j0 := eq768 x
       grind)
    | (have r₁ := eq768 x
       have r₂ := eq24177
       grind)
    | exact resolve eq768 eq24177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq24203 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq24198
  have eq24229 : y = (M.op x (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq24203
       grind)
    | exact superpose eq24203 eq177
    | exact resolve eq177 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24240 : ∀ X0 : G, (M.op x (M.op X0 (M.op x X0))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq24203
       grind)
    | exact superpose eq24203 eq16
    | exact resolve eq16 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24283 : x = (M.op x (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19525 eq24229
    | exact resolve eq24229 eq19525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19525 eq24229
  have eq24438 : x = (M.op (M.op x (M.op x y)) (k x (M.op x x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24283 eq988
    | exact resolve eq988 eq24283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24441 : x = (M.op (M.op x (M.op x y)) (k x x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24203 eq24438
    | exact resolve eq24438 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24438
  have eq24451 : x = (M.op (M.op x (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24177 eq24441
    | exact resolve eq24441 eq24177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24441
  have eq27094 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24283 eq24240
    | exact resolve eq24240 eq24283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24240 eq24283
  have eq27149 : (M.op x (M.op x y)) = (M.op x (M.op (M.op x (M.op x y)) x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq27094
  have eq27162 : (M.op x x) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24451 eq27149
    | exact resolve eq27149 eq24451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24451 eq27149
  have eq27166 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24203 eq27162
    | exact resolve eq27162 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27162
  have eq27186 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27166 eq180
    | exact resolve eq180 eq27166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq27198 : x = (M.op (M.op x y) (k x (M.op x x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27166 eq988
    | exact resolve eq988 eq27166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27204 : x = (M.op (M.op x y) (k x x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24203 eq27198
    | exact resolve eq27198 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27198
  have eq27210 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27166 eq27186
    | exact resolve eq27186 eq27166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27166 eq27186
  have eq27215 : x = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24177 eq27204
    | exact resolve eq27204 eq24177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24177 eq27204
  have eq27247 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27210 eq16
    | exact resolve eq16 eq27210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27210
  have eq27275 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27215 eq27247
    | exact resolve eq27247 eq27215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27247
  have eq27418 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27215 eq16
    | exact resolve eq16 eq27215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27215
  have eq27447 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq24203 eq27418
    | exact resolve eq27418 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24203 eq27418
  have eq27455 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27275 eq27447
    | exact resolve eq27447 eq27275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27275 eq27447
  have eq27456 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq27455
  have eq27462 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27456 eq28
    | exact resolve eq28 eq27456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27456
  have eq27553 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq27462
    | exact resolve eq27462 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27462
  have eq27554 : x = (M.op x y) := by grind
  clear eq27553
  have eq27579 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27554
       grind)
    | exact superpose eq27554 eq18
    | exact resolve eq18 eq27554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27580 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq27554
       grind)
    | exact superpose eq27554 eq22
    | exact resolve eq22 eq27554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27583 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq27554
       grind)
    | exact superpose eq27554 eq177
    | exact resolve eq177 eq27554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq27593 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq27554
       grind)
    | exact superpose eq27554 eq378
    | exact resolve eq378 eq27554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq27554
  have eq27624 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq27580 eq20
    | exact resolve eq20 eq27580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27580
  have eq28050 : (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq27579 eq569
    | exact resolve eq569 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq28053 : ∀ X0 : G, (M.op y (M.op X0 (M.op (k y (M.op x y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27579 eq585
    | exact resolve eq585 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq28057 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 y)) (k y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq27579 eq1081
    | exact resolve eq1081 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq28058 : y = (M.op (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | exact superpose eq27579 eq1095
    | exact resolve eq1095 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095
  have eq28059 : y = (M.op y (k y (M.op x y))) := by
    first
    | exact superpose eq27579 eq2482
    | exact resolve eq2482 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq28066 : y = (M.op (M.op x y) (k y (M.op x y))) := by
    first
    | exact superpose eq27579 eq637
    | exact resolve eq637 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq28129 : ∀ X0 : G, (M.op (k y (M.op x y)) (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq28050 eq16
    | exact resolve eq16 eq28050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28146 : (k y (M.op x y)) = (M.op (M.op x y) (k (k y (M.op x y)) (M.op (k y (M.op x y)) (k y (M.op x y))))) := by
    first
    | exact superpose eq28050 eq988
    | exact resolve eq988 eq28050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq28147 : (k y (M.op x y)) = (M.op (M.op x y) (k (k y (M.op x y)) y)) := by
    first
    | exact superpose eq28058 eq28146
    | exact resolve eq28146 eq28058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28146
  have eq28236 : (k y (M.op x y)) = (M.op (M.op x y) (M.op (k y (M.op x y)) y)) := by
    first
    | exact superpose eq28059 eq174
    | exact resolve eq174 eq28059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq28248 : (k y (M.op x y)) = (M.op y (k (k y (M.op x y)) (M.op (k y (M.op x y)) (k y (M.op x y))))) := by
    first
    | exact superpose eq28059 eq570
    | exact resolve eq570 eq28059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28059
  have eq28263 : (k y (M.op x y)) = (M.op y (k (k y (M.op x y)) y)) := by
    first
    | exact superpose eq28058 eq28248
    | exact resolve eq28248 eq28058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28058 eq28248
  have eq29271 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op (M.op X0 (M.op y (M.op x y))) (k (M.op y (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq27583 eq570
    | exact resolve eq570 eq27583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq29277 : (M.op y (M.op x y)) = (M.op (M.op y (M.op x y)) (k (M.op y (M.op x y)) y)) := by
    first
    | exact superpose eq27583 eq2470
    | exact resolve eq2470 eq27583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2470 eq27583
  have eq29308 : (k y (M.op x y)) = (M.op (k y (M.op x y)) (k (k y (M.op x y)) y)) := by
    first
    | exact superpose eq28050 eq29277
    | exact resolve eq29277 eq28050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29277
  have eq29314 : ∀ X0 : G, (k y (M.op x y)) = (M.op (M.op X0 (k y (M.op x y))) (k (k y (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq28050 eq29271
    | exact resolve eq29271 eq28050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28050 eq29271
  have eq31008 : ∀ X0 X1 : G, (M.op (k (k y (M.op x y)) y) (k y (M.op x y))) = (M.op (M.op X0 (M.op X1 y)) (M.op (M.op (k (k y (M.op x y)) y) (k y (M.op x y))) (k (k y (M.op x y)) y))) := by
    intro X0 X1
    first
    | exact superpose eq28263 eq179
    | exact resolve eq179 eq28263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq28263
  have eq31029 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) (k y (M.op x y))) = (M.op (k (k y (M.op x y)) y) (k y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq29314 eq31008
    | exact resolve eq31008 eq29314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29314 eq31008
  have eq31036 : y = (M.op (k (k y (M.op x y)) y) (k y (M.op x y))) := by
    first
    | exact superpose eq28057 eq31029
    | exact resolve eq31029 eq28057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28057 eq31029
  have eq36517 : (k (k y (M.op x y)) y) = (M.op y (M.op (k (k y (M.op x y)) y) (k y (M.op x y)))) := by
    first
    | exact superpose eq29308 eq28053
    | exact resolve eq28053 eq29308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28053 eq29308
  have eq36555 : (M.op y y) = (k (k y (M.op x y)) y) := by
    first
    | exact superpose eq31036 eq36517
    | exact resolve eq36517 eq31036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31036 eq36517
  have eq36562 : (M.op (M.op x y) y) = (k (k y (M.op x y)) y) := by
    first
    | (have i₁ := eq36555
       have i₂ := eq182
       grind)
    | exact superpose eq182 eq36555
    | exact resolve eq36555 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq36555
  have eq36565 : (M.op x y) = (k (k y (M.op x y)) y) := by
    first
    | exact superpose eq27579 eq36562
    | exact resolve eq36562 eq27579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27579 eq36562
  have eq36573 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq36565 eq28147
    | exact resolve eq28147 eq36565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28147 eq36565
  have eq36615 : (M.op x y) = (M.op (k y (M.op x y)) (M.op (M.op x y) (k y (M.op x y)))) := by
    first
    | exact superpose eq36573 eq28129
    | exact resolve eq28129 eq36573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28129
  have eq36628 : ∀ X0 : G, (k y (M.op x y)) ≠ X0 ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq36573 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (k y (M.op x y))
       have r₂ := eq36573
       grind)
    | exact resolve eq13 eq36573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36629 : (k (M.op x y) (k y (M.op x y))) = (M.op (M.op x y) (k y (M.op x y))) := by
    first
    | exact superpose eq36573 eq181
    | exact resolve eq181 eq36573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36638 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq36573 eq11
    | exact resolve eq11 eq36573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36657 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by grind
  clear eq36638
  have eq36669 : y = (k (M.op x y) (k y (M.op x y))) := by
    first
    | exact superpose eq28066 eq36629
    | exact resolve eq36629 eq28066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36629
  have eq36676 : (M.op x y) = (M.op (k y (M.op x y)) y) := by
    first
    | exact superpose eq28066 eq36615
    | exact resolve eq36615 eq28066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28066 eq36615
  have eq38528 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (k (M.op x y) (M.op x y)) y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq36657 eq28236
    | exact resolve eq28236 eq36657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28236
  have eq38546 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq36657 eq36676
    | exact resolve eq36676 eq36657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36657 eq36676
  have eq38572 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq38546 eq38528
    | exact resolve eq38528 eq38546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38528 eq38546
  have eq38596 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq36628 (M.op x y)
       grind)
    | (have r₁ := eq38572
       have r₂ := eq36628 (M.op x y)
       grind)
    | exact resolve eq38572 eq36628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36628 eq38572
  have eq38646 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq38596 eq36573
    | exact resolve eq36573 eq38596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36573 eq38596
  have eq38765 : y = (k (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq38646 eq36669
    | exact resolve eq36669 eq38646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36669 eq38646
  have eq39039 : (σ y) = (k (σ (M.op x y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq38765 eq27593
    | exact resolve eq27593 eq38765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27593 eq38765
  have eq39047 : (σ y) = (k (σ (M.op x y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq20 eq39039
    | exact resolve eq39039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq39039
  have eq39051 : (σ y) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq27624 eq39047
    | exact resolve eq39047 eq27624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39047
  have eq39055 : (σ y) = (k (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq39051
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39051
    | exact resolve eq39051 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq39051
  have eq39247 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39055 eq2501
    | (have j0 := eq2501 (σ x)
       grind)
    | exact resolve eq2501 eq39055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501
  have eq39253 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq39247
    | exact resolve eq39247 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39247
  have eq39279 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39253 eq181
    | exact resolve eq181 eq39253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq39317 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39253 eq39279
    | exact resolve eq39279 eq39253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39279
  have eq39346 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39317 eq39055
    | exact resolve eq39055 eq39317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39055
  have eq39371 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39317 eq39346
    | exact resolve eq39346 eq39317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39317 eq39346
  have eq39391 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39371 eq27
    | exact resolve eq27 eq39371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39371
  have eq39415 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq39391
       have r₂ := eq27624
       grind)
    | exact resolve eq39391 eq27624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39391
  have eq39418 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39415 eq26
    | exact resolve eq26 eq39415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq39415
  have eq39952 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39418 eq39253
    | exact resolve eq39253 eq39418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39253 eq39418
  have eq39991 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq39952
  have eq40008 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq39991 eq27
    | exact resolve eq27 eq39991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39991
  have eq40045 : False := by grind
  exact eq40045

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxx_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  clear eq36
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq16
    | exact resolve eq16 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq174 (M.op y y)
       have i₂ := eq16 y y y
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq189
       have i₂ := eq183 y
       grind)
    | exact superpose eq183 eq189
    | exact resolve eq189 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq195 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (k (σ y) (σ y)))) := by
    first
    | (have i₁ := eq175 sF3
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq175
    | exact resolve eq175 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq206 : y = (M.op (k x x) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq177
    | exact resolve eq177 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq180
    | exact resolve eq180 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ y) (k (σ y) (σ y))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq195 eq16
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq220 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq220
    | exact resolve eq220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (k X0 X0)
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq16
    | exact resolve eq16 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0 (k X0 X0)
       have i₂ := eq220 X0
       grind)
    | exact superpose eq220 eq186
    | exact resolve eq186 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq186
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = (M.op X0 (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq180 (M.op X0 (k X0 X0)) (M.op x X0)
       have i₂ := eq186 X0 x
       grind)
    | exact superpose eq186 eq180
    | exact resolve eq180 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq653 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X0 (k X0 X0)) X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq16 X2 (M.op x X0) (M.op X0 (k X0 X0))
       have i₂ := eq186 X0 x
       grind)
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (M.op X0 (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq649 X0
       have i₂ := eq271 X0 X0
       grind)
    | exact superpose eq271 eq649
    | exact resolve eq649 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq649
  have eq668 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ X0) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq656 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq656
    | exact resolve eq656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq750 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq750
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq750
    | exact resolve eq750 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq853 : (M.op x y) = (k y x) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq745
       have i₂ := eq183 y
       grind)
    | exact superpose eq183 eq745
    | exact resolve eq745 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq1048 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 X0) X1 X0
       have i₂ := eq638 X0
       grind)
    | exact superpose eq638 eq16
    | exact resolve eq16 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = (M.op X0 (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1048 (M.op X0 (k X0 X0)) (k X0 X0)
       have i₂ := eq638 X0
       grind)
    | exact superpose eq638 eq1048
    | exact resolve eq1048 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq1048
  have eq1121 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1083 X0
       have i₂ := eq656 X0
       grind)
    | exact superpose eq656 eq1083
    | exact resolve eq1083 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083
  have eq2032 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq853
       grind)
    | exact superpose eq853 eq39
    | exact resolve eq39 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq2033 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq2032
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2032
    | exact resolve eq2032 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2035 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq2033
    | exact resolve eq2033 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq3040 : (M.op (M.op (σ y) (k (σ y) (σ y))) (k (M.op (σ y) (k (σ y) (σ y))) (M.op (σ y) (k (σ y) (σ y))))) = (M.op (σ y) (M.op (M.op (M.op (σ y) (k (σ y) (σ y))) (k (M.op (σ y) (k (σ y) (σ y))) (M.op (σ y) (k (σ y) (σ y))))) (M.op (σ y) (k (σ y) (σ y))))) := by
    first
    | (have i₁ := eq257 (M.op (M.op sF3 (k sF3 sF3)) (k (M.op sF3 (k sF3 sF3)) (M.op sF3 (k sF3 sF3))))
       have i₂ := eq656 (M.op sF3 (k sF3 sF3))
       grind)
    | exact superpose eq656 eq257
    | exact resolve eq257 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq3066 : (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) = (M.op (σ y) (M.op (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) (M.op (σ y) (k (σ y) (σ y))))) := by
    first
    | (have i₁ := eq3040
       have i₂ := eq1121 sF3
       grind)
    | exact superpose eq1121 eq3040
    | exact resolve eq3040 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3072 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq3066
       have i₂ := eq186 sF3 (M.op sF3 (k sF3 sF3))
       grind)
    | exact superpose eq186 eq3066
    | exact resolve eq3066 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066
  have eq3076 : (k (σ y) (σ y)) = (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq3072
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq3072
    | exact resolve eq3072 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072
  have eq3254 : ∀ X0 X1 : G, (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) (M.op (σ y) (k (σ y) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq195 eq179
    | exact resolve eq179 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq3306 : ∀ X0 X1 : G, (M.op (M.op (σ y) (k (σ y) (σ y))) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq3254 X0 X1
       have i₂ := eq186 sF3 (M.op sF3 (k sF3 sF3))
       grind)
    | exact superpose eq186 eq3254
    | exact resolve eq3254 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3254
  have eq3334 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq3076 eq3306
    | exact resolve eq3306 eq3076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076 eq3306
  have eq3353 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq3334 X0 (k sF4 sF4)
       have i₂ := eq220 sF4
       grind)
    | exact superpose eq220 eq3334
    | exact resolve eq3334 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3334
  have eq3643 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0)))) = (M.op X0 (M.op (M.op (M.op X0 (k X0 X0)) (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0)))) (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq653 X0 (M.op (M.op X0 (k X0 X0)) (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))))
       have i₂ := eq656 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq656 eq653
    | exact resolve eq653 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653 eq656
  have eq3687 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) X0) = (M.op X0 (M.op (M.op (M.op X0 (k X0 X0)) X0) (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq3643 X0
       have i₂ := eq1121 X0
       grind)
    | exact superpose eq1121 eq3643
    | exact resolve eq3643 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121 eq3643
  have eq3695 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq3687 X0
       have i₂ := eq186 X0 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq186 eq3687
    | exact resolve eq3687 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq3687
  have eq3700 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq3695 X0
       have i₂ := eq183 X0
       grind)
    | exact superpose eq183 eq3695
    | exact resolve eq3695 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq3703 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (M.op (σ X0) (σ (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3700 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq3700
    | exact resolve eq3700 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3700
  have eq9216 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ (k X0 X0))) (σ X0)) = (M.op (M.op X1 (M.op X2 (σ X0))) (M.op (M.op (M.op (σ X0) (σ (k X0 X0))) (σ X0)) (M.op (σ X0) (σ (k X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq179 (M.op (σ X0) (σ (k X0 X0))) X1 X2 (σ X0)
       have i₂ := eq668 X0
       grind)
    | exact superpose eq668 eq179
    | exact resolve eq179 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq668
  have eq9231 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) (σ (k X0 X0))) (σ X0)) = (M.op (M.op X1 (M.op X2 (σ X0))) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9216 X0 X1 X2
       have i₂ := eq647 X0 (M.op (σ X0) (σ (k X0 X0)))
       grind)
    | exact superpose eq647 eq9216
    | exact resolve eq9216 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq9216
  have eq9274 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op (M.op X1 (M.op X2 (σ X0))) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9231 X0 X1 X2
       have i₂ := eq3703 X0
       grind)
    | exact superpose eq3703 eq9231
    | exact resolve eq9231 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703 eq9231
  have eq21646 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (τ X0))) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9274 (τ X0) X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq9274
    | exact resolve eq9274 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9274
  have eq21732 : ∀ X0 X1 X2 : G, (k (σ (τ X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21646 X0 X1 X2
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq21646
    | exact resolve eq21646 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq21646
  have eq21764 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21732 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq21732
    | exact resolve eq21732 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21732
  have eq22254 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21764 (M.op X1 X0) (k X1 X1) X0
       have i₂ := eq187 X1 X0
       grind)
    | exact superpose eq187 eq21764
    | exact resolve eq21764 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22257 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq206 eq21764
    | exact resolve eq21764 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq21764
  have eq22469 : ∀ X0 : G, y = (M.op (M.op X0 x) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq22257 eq177
    | exact resolve eq177 eq22257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq22257
  have eq28213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2035 eq848
    | exact resolve eq848 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq28224 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq28213
       have r₂ := eq27
       grind)
    | exact resolve eq28213 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28213
  have eq28239 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28224 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28224
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28224
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28224
       grind)
    | exact resolve eq13 eq28224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28265 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28224 eq22254
    | exact resolve eq22254 eq28224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28286 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq28239
       have r₂ := eq26
       grind)
    | exact resolve eq28239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28239
  have eq28299 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq28286
       have i₂ := eq183 sF3
       grind)
    | exact superpose eq183 eq28286
    | exact resolve eq28286 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28286
  have eq28309 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2035 eq28299
    | exact resolve eq28299 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035 eq28299
  have eq28314 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28309 eq115
    | exact resolve eq115 eq28309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq28309
  have eq28396 : x = (k y y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq29 eq28314
    | exact resolve eq28314 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28314
  have eq28397 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq28396
  have eq28439 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (M.op (σ y) X0))) = X0 ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq28397 eq187
    | exact resolve eq187 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq29990 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28224 eq28439
    | exact resolve eq28439 eq28224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28224 eq28439
  have eq30038 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) := by grind
  clear eq29990
  have eq30071 : (σ x) = (M.op (σ (M.op x y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq28265 eq30038
    | exact resolve eq30038 eq28265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28265 eq30038
  have eq30094 : (σ x) = (M.op (σ (M.op x y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28397 eq30071
    | exact resolve eq30071 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30071
  have eq32384 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30094 eq3353
    | exact resolve eq3353 eq30094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353 eq30094
  have eq32440 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq32384
    | exact resolve eq32384 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32384
  have eq32461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq28397 eq32440
    | exact resolve eq32440 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28397 eq32440
  have eq32475 : (M.op x y) = (M.op y x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq32461
       have r₂ := eq27
       grind)
    | exact resolve eq32461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32461
  have eq32483 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq32475
       grind)
    | exact superpose eq32475 eq174
    | exact resolve eq174 eq32475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq32484 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22469 y
       have i₂ := eq32475
       grind)
    | exact superpose eq32475 eq22469
    | exact resolve eq22469 eq32475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22469
  have eq32514 : (k (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22254 x y
       have i₂ := eq32475
       grind)
    | exact superpose eq32475 eq22254
    | exact resolve eq22254 eq32475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22254 eq32475
  have eq32536 : x = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32514 eq32483
    | exact resolve eq32483 eq32514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32483 eq32514
  have eq33087 : x = y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq32536 eq32484
    | exact resolve eq32484 eq32536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32484 eq32536
  have eq33129 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq33087
  have eq33244 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq220 y
       have i₂ := eq33129
       grind)
    | exact superpose eq33129 eq220
    | exact resolve eq220 eq33129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq33129
  have eq33282 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33244
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33244
    | exact resolve eq33244 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33244
  have eq34818 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq33282 eq28
    | exact resolve eq28 eq33282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33282
  have eq34987 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq34818
    | exact resolve eq34818 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34818
  have eq34988 : x = (M.op x y) ∨ x = y := by grind
  clear eq34987
  have eq35012 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq34988
       grind)
    | exact superpose eq34988 eq18
    | exact resolve eq18 eq34988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35013 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq34988
       grind)
    | exact superpose eq34988 eq22
    | exact resolve eq22 eq34988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34988
  have eq35081 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq35013
    | exact resolve eq35013 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35013
  have eq35082 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq192 eq35012
    | exact resolve eq35012 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq35012
  have eq35269 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq267 y
       have i₂ := eq35082
       grind)
    | exact superpose eq35082 eq267
    | exact resolve eq267 eq35082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq35082
  have eq35308 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq35269
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35269
    | exact resolve eq35269 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35269
  have eq35332 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq35308
    | exact resolve eq35308 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35308
  have eq35347 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq35081 eq35332
    | exact resolve eq35332 eq35081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35332
  have eq35355 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq35347
    | exact resolve eq35347 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35347
  have eq35360 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq35355 eq27
    | exact resolve eq27 eq35355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35355
  have eq35474 : x = y := by
    first
    | (have r₁ := eq35360
       have r₂ := eq35081
       grind)
    | exact resolve eq35360 eq35081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35081 eq35360
  have eq35496 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35474
       grind)
    | exact superpose eq35474 eq18
    | exact resolve eq18 eq35474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35497 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq35474
       grind)
    | exact superpose eq35474 eq24
    | exact resolve eq24 eq35474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35474
  have eq35607 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq35497
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35497
    | exact resolve eq35497 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35497
  have eq35608 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq35496
       have i₂ := eq183 x
       grind)
    | exact superpose eq183 eq35496
    | exact resolve eq35496 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35496
  have eq35618 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35607 eq26
    | exact resolve eq26 eq35607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35607
  have eq35833 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35618
       have i₂ := eq183 sF2
       grind)
    | exact superpose eq183 eq35618
    | exact resolve eq35618 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq35618
  have eq35935 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq35608
       grind)
    | exact superpose eq35608 eq39
    | exact resolve eq39 eq35608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq35608
  have eq35978 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35935
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35935
    | exact resolve eq35935 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35935
  have eq35995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35833 eq35978
    | exact resolve eq35978 eq35833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35833 eq35978
  have eq36004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq35995
    | exact resolve eq35995 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35995
  have eq36009 : False := by grind
  exact eq36009

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pyy_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq73 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq72
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq72
    | exact resolve eq72 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq102
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq102 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq251 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq68 (τ X0)
       grind)
    | exact superpose eq68 eq34
    | exact resolve eq34 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq392 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq381 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq381
    | exact resolve eq381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq394 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq392 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq392
    | exact resolve eq392 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq392
  have eq520 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq52 y X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq52 sF3 x x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (σ X0) (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq56
    | exact resolve eq56 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq697 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq394 X0
       grind)
    | exact superpose eq394 eq16
    | exact resolve eq16 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq779 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq789 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq883 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0) (τ X0)
       have i₂ := eq697 X0
       grind)
    | exact superpose eq697 eq56
    | exact resolve eq56 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq1055 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq267 sF4
       have i₂ := eq56 sF4 sF3
       grind)
    | exact superpose eq56 eq267
    | exact resolve eq267 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq1546 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq281 X0 x x
       grind)
    | exact superpose eq281 eq56
    | exact resolve eq56 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1554 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1546 X0
       have i₂ := eq281 X0 X0 X0
       grind)
    | exact superpose eq281 eq1546
    | exact resolve eq1546 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546
  have eq4010 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq779 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1554 sF0
       grind)
    | exact superpose eq1554 eq779
    | exact resolve eq779 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4041 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq4010
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq4010
    | exact resolve eq4010 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010
  have eq4046 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq4041 eq779
    | exact resolve eq779 eq4041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq4041
  have eq4079 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq4046 eq14
    | exact resolve eq14 eq4046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4116 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq780 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1554 sF4
       grind)
    | exact superpose eq1554 eq780
    | exact resolve eq780 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4147 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4116
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq4116
    | exact resolve eq4116 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116
  have eq4171 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4147 eq780
    | exact resolve eq780 eq4147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4280 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4079 eq50
    | exact resolve eq50 eq4079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079
  have eq4323 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq4280 eq4046
    | exact resolve eq4046 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4046 eq4280
  have eq4492 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq1055 eq251
    | exact resolve eq251 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq1055
  have eq4530 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq4492 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq4492
    | exact resolve eq4492 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4492
  have eq4531 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4530 x
       have i₂ := eq56 sF4 x
       grind)
    | exact superpose eq56 eq4530
    | exact resolve eq4530 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530
  have eq4532 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4147 eq4531
    | exact resolve eq4531 eq4147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147 eq4531
  have eq4533 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4532 eq4171
    | exact resolve eq4171 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4171
  have eq5872 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq520 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq281 X0 x X2
       grind)
    | exact superpose eq281 eq520
    | exact resolve eq520 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq5981 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5872 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5872
    | exact resolve eq5872 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5872
  have eq5994 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5981 X0 x
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq5981
    | exact resolve eq5981 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5981
  have eq7228 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq789 X0 X1 X2 X3
       have i₂ := eq5994 X0
       grind)
    | exact superpose eq5994 eq789
    | exact resolve eq789 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq7299 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7228 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq281 X0 x x
       grind)
    | exact superpose eq281 eq7228
    | exact resolve eq7228 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7228
  have eq7529 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7299 X0 X1 X2
       have i₂ := eq281 X0 X0 X0
       grind)
    | exact superpose eq281 eq7299
    | exact resolve eq7299 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299
  have eq7567 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7529 X0 X1 X2
       have i₂ := eq5994 X0
       grind)
    | exact superpose eq5994 eq7529
    | exact resolve eq7529 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5994 eq7529
  have eq7626 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7567 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7567
    | (have j0 := eq7567 y X0 x
       grind)
    | exact resolve eq7567 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7638 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq7567
    | (have j0 := eq7567 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7567 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7716 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq780 X0
       have i₂ := eq7567 X0 X0 sF4
       grind)
    | exact superpose eq7567 eq780
    | exact resolve eq780 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq9304 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 X1
       have i₂ := eq7567 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7567 eq528
    | exact resolve eq528 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq9365 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq9304 X0 x
       grind)
    | exact superpose eq9304 eq52
    | exact resolve eq52 eq9304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9304
  have eq9515 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9365 (M.op X0 (M.op X0 X0))
       have i₂ := eq281 X0 X0 X0
       grind)
    | exact superpose eq281 eq9365
    | exact resolve eq9365 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9365
  have eq9675 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1554 X0
       have i₂ := eq9515 X0
       grind)
    | exact superpose eq9515 eq1554
    | exact resolve eq1554 eq9515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq9677 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq9515 X0
       grind)
    | exact superpose eq9515 eq14
    | exact resolve eq14 eq9515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9700 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7716 sF4
       have i₂ := eq9515 sF4
       grind)
    | exact superpose eq9515 eq7716
    | exact resolve eq7716 eq9515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7716
  have eq9777 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9515 eq14
    | exact resolve eq14 eq9515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9811 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9777 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq9777
    | exact resolve eq9777 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9777
  have eq9853 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4532 eq9700
    | exact resolve eq9700 eq4532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532 eq9700
  have eq9933 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq7567 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7567 eq529
    | exact resolve eq529 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq7567
  have eq10257 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9933 eq52
    | exact resolve eq52 eq9933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9933
  have eq10421 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq10257 (M.op X0 (M.op X0 X0))
       have i₂ := eq281 X0 X0 X0
       grind)
    | exact superpose eq281 eq10257
    | exact resolve eq10257 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10257
  have eq10768 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq787 X0 X1 X2
       have i₂ := eq9811 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq9811 eq787
    | exact resolve eq787 eq9811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq9811
  have eq10769 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4323 eq10768
    | exact resolve eq10768 eq4323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10768
  have eq10770 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7626 eq10769
    | exact resolve eq10769 eq7626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7626 eq10769
  have eq11052 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq10421 eq14
    | exact resolve eq14 eq10421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10421
  have eq11086 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11052 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq11052
    | exact resolve eq11052 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11052
  have eq11235 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq10770 (M.op x (M.op x x)) x x
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq10770
    | exact resolve eq10770 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10770
  have eq11789 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq11086 eq788
    | exact resolve eq788 eq11086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq11086
  have eq11790 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4533 eq11789
    | exact resolve eq11789 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533 eq11789
  have eq11791 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7638 eq11790
    | exact resolve eq11790 eq7638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7638 eq11790
  have eq11819 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq11791 (M.op x (M.op x x)) x sF2
       have i₂ := eq52 x x sF2
       grind)
    | exact superpose eq52 eq11791
    | exact resolve eq11791 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11791
  have eq13732 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9853 eq11819
    | exact resolve eq11819 eq9853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9853 eq11819
  have eq15619 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq883 (M.op X0 (M.op X0 X0))
       have i₂ := eq281 X0 X0 X0
       grind)
    | exact superpose eq281 eq883
    | exact resolve eq883 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq22494 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) := by
    first
    | exact superpose eq30 eq15619
    | exact resolve eq15619 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq22495 : x = (M.op x (τ (M.op (σ x) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq28 eq15619
    | exact resolve eq15619 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15619
  have eq22595 : x = (M.op x (τ (M.op y (M.op (M.op x y) (σ x))))) := by
    first
    | (have i₁ := eq22495
       have i₂ := eq9515 sF2
       grind)
    | exact superpose eq9515 eq22495
    | exact resolve eq22495 eq9515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22495
  have eq22596 : (M.op x y) = (M.op (M.op x y) (τ (M.op y (M.op (M.op x y) (σ (M.op x y)))))) := by
    first
    | (have i₁ := eq22494
       have i₂ := eq9515 sF1
       grind)
    | exact superpose eq9515 eq22494
    | exact resolve eq22494 eq9515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9515 eq22494
  have eq23277 : (M.op (M.op x y) (M.op y (M.op x y))) = (τ (M.op y (M.op (M.op x y) (σ (M.op x y))))) := by
    first
    | exact superpose eq22596 eq9677
    | exact resolve eq9677 eq22596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22596
  have eq23288 : (M.op y (M.op y (M.op x y))) = (τ (M.op y (M.op (M.op x y) (σ (M.op x y))))) := by
    first
    | exact superpose eq4323 eq23277
    | exact resolve eq23277 eq4323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4323 eq23277
  have eq32611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32612 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq32611
    | exact resolve eq32611 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32611
  have eq32623 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq32612
       have r₂ := eq27
       grind)
    | exact resolve eq32612 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32612
  have eq32627 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq32623
    | exact resolve eq32623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32623
  have eq32631 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq32627
    | exact resolve eq32627 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32627
  have eq32637 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq32631 eq51
    | exact resolve eq51 eq32631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq32646 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq32631 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq32631
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq32631
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq32631
       grind)
    | exact resolve eq13 eq32631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32631
  have eq32696 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq32646
       have r₂ := eq26
       grind)
    | exact resolve eq32646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32646
  have eq33004 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq32637 eq14
    | exact resolve eq14 eq32637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32637
  have eq33081 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq33004 x
       have i₂ := eq56 sF2 x
       grind)
    | exact superpose eq56 eq33004
    | exact resolve eq33004 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33004
  have eq34431 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq32696 eq120
    | exact resolve eq120 eq32696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq32696
  have eq34439 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34431
  have eq34857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34439 eq33081
    | exact resolve eq33081 eq34439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33081 eq34439
  have eq34938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq34857
  have eq34957 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34938
       have r₂ := eq27
       grind)
    | exact resolve eq34938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34938
  have eq34982 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq34957
       grind)
    | exact superpose eq34957 eq50
    | exact resolve eq50 eq34957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq34957
  have eq36216 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq34982 eq14
    | exact resolve eq14 eq34982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34982
  have eq36295 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36216 x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq36216
    | exact resolve eq36216 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36216
  have eq36764 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq36295
       grind)
    | exact superpose eq36295 eq56
    | exact resolve eq56 eq36295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq36295
  have eq36852 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36764 eq9677
    | exact resolve eq9677 eq36764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9677 eq36764
  have eq36916 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq53 eq36852
    | exact resolve eq36852 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq36852
  have eq36980 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36916 eq13732
    | exact resolve eq13732 eq36916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13732 eq36916
  have eq36999 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq9675 eq36980
    | exact resolve eq36980 eq9675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9675 eq36980
  have eq38485 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36999 eq883
    | exact resolve eq883 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq36999
  have eq38579 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq38485
    | exact resolve eq38485 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq38485
  have eq38595 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq38579
    | exact resolve eq38579 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq38579
  have eq38600 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq38595
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38595
    | exact resolve eq38595 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38595
  have eq38601 : x = (M.op x y) ∨ x = y := by grind
  clear eq38600
  have eq38603 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq38601 eq20
    | exact resolve eq20 eq38601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38601
  have eq38801 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq38603
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38603
    | exact resolve eq38603 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38603
  have eq39009 : x = (M.op x (τ (M.op y (M.op (M.op x y) (σ (M.op x y)))))) ∨ x = y := by
    first
    | exact superpose eq38801 eq22595
    | exact resolve eq22595 eq38801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22595
  have eq39023 : x = (M.op x (M.op y (M.op y (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq23288 eq39009
    | exact resolve eq39009 eq23288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23288 eq39009
  have eq39076 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq11235 eq39023
    | exact resolve eq39023 eq11235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235 eq39023
  have eq39352 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq554 y
       have i₂ := eq39076
       grind)
    | exact superpose eq39076 eq554
    | exact resolve eq554 eq39076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq39076
  have eq39449 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39352
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39352
    | exact resolve eq39352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39352
  have eq39462 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq39449
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39449
    | exact resolve eq39449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39449
  have eq39466 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq39462
    | exact resolve eq39462 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39462
  have eq39467 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq39466 eq27
    | exact resolve eq27 eq39466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39466
  have eq39558 : x = y := by
    first
    | (have r₁ := eq39467
       have r₂ := eq38801
       grind)
    | exact resolve eq39467 eq38801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38801 eq39467
  have eq39560 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq39558
       grind)
    | exact superpose eq39558 eq18
    | exact resolve eq18 eq39558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq39561 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq39558
       grind)
    | exact superpose eq39558 eq24
    | exact resolve eq24 eq39558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq39558
  have eq39757 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq39561
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39561
    | exact resolve eq39561 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq39561
  have eq39955 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39757 eq26
    | exact resolve eq26 eq39757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq39757
  have eq40395 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq39955 eq73
    | exact resolve eq73 eq39955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq39955
  have eq40533 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40395
       have i₂ := eq39560
       grind)
    | exact superpose eq39560 eq40395
    | exact resolve eq40395 eq39560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39560 eq40395
  have eq40587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40533 eq15
    | exact resolve eq15 eq40533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40533
  have eq40642 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq40587
    | exact resolve eq40587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq40587
  have eq40661 : False := by grind
  exact eq40661

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_pyx_pxy_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq80 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq91 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq100 : ∀ X0 : G, (σ (k X0 (k y x))) = (k (σ X0) (k (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (σ (k (k y x) X0)) = (k (k (σ y) (σ x)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x) X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq10
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq117 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq117 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | (have j0 := eq117 y x
       grind)
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq117
    | (have j0 := eq117 (σ y) (σ x)
       grind)
    | exact resolve eq117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) := by
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
  have eq172 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq138 eq16
    | exact resolve eq16 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq50 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq442 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq342
    | exact resolve eq342 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq512 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 X0 (M.op X0 X1)
       have i₂ := eq56 (M.op X0 X1) X1
       grind)
    | exact superpose eq56 eq52
    | exact resolve eq52 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq52 y X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq52 sF3 x x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq694 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X0)) X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op (M.op X0 (M.op y X0)) X0) (M.op X0 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq55
    | exact resolve eq55 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq56 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 x (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq55 X0 X1 x X1
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) (M.op X2 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 (M.op X1 X2)) X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq55 (M.op X0 (M.op X1 X2)) X0 X1 X2
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op x (M.op x X1))
       have i₂ := eq55 X0 x x X1
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq826 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X0)) (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X1) X2 (σ X0)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq14
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq14 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq840 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq826 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq826 X0 X1
       have r₂ := eq13 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq826 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq826 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq849 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       have j1 := eq117 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq840 X0 X1
       have r₂ := eq117 (σ X0) (σ X1)
       grind)
    | exact resolve eq840 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq849
    | (have j0 := eq849 X0 X1
       grind)
    | exact resolve eq849 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1224 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq253 X0 x x
       grind)
    | exact superpose eq253 eq56
    | exact resolve eq56 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1229 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1224 X0
       have i₂ := eq253 X0 X0 X0
       grind)
    | exact superpose eq253 eq1224
    | exact resolve eq1224 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224
  have eq3736 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq683 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1229 sF0
       grind)
    | exact superpose eq1229 eq683
    | exact resolve eq683 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3765 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3736
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3736
    | exact resolve eq3736 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq3769 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3765 eq683
    | exact resolve eq683 eq3765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3765
  have eq3795 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3769 eq14
    | exact resolve eq14 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769
  have eq3828 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq684 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1229 sF4
       grind)
    | exact superpose eq1229 eq684
    | exact resolve eq684 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3857 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3828
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3828
    | exact resolve eq3828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828
  have eq3877 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3857 eq684
    | exact resolve eq684 eq3857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq3857
  have eq3903 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3877 eq14
    | exact resolve eq14 eq3877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3966 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3795 eq50
    | exact resolve eq50 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4125 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3903 eq51
    | exact resolve eq51 eq3903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq3903
  have eq4162 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4125 eq3877
    | exact resolve eq3877 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877
  have eq4540 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) (M.op X0 (M.op x y))) = (M.op y (M.op (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) (M.op X0 (M.op x y))) (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq683 (M.op (M.op X0 sF0) (M.op (M.op X0 sF0) (M.op X0 sF0)))
       have i₂ := eq513 X0 sF0
       grind)
    | exact superpose eq513 eq683
    | exact resolve eq683 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq683
  have eq4547 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op (M.op X0 (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y)))) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4540 X0
       have i₂ := eq14 (M.op X0 sF0) (M.op (M.op X0 sF0) (M.op (M.op X0 sF0) (M.op X0 sF0))) (M.op X0 sF0)
       grind)
    | exact superpose eq14 eq4540
    | exact resolve eq4540 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4540
  have eq4830 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq856 (τ X1) (τ X0)
       have i₂ := eq442 X0 X1
       grind)
    | exact superpose eq442 eq856
    | exact resolve eq856 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq5002 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4830 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq4830
    | (have j0 := eq4830 X0 X1
       grind)
    | exact resolve eq4830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq5088 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5002 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5002
    | (have j0 := eq5002 X0 X1
       grind)
    | exact resolve eq5002 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq5170 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5088 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5088
    | (have j0 := eq5088 X0 X1
       grind)
    | exact resolve eq5088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088
  have eq5178 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5170 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5170
    | (have j0 := eq5170 X0 X1
       grind)
    | exact resolve eq5170 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5170
  have eq5185 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5178 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq5178
    | (have j0 := eq5178 X0 X1
       grind)
    | exact resolve eq5178 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178
  have eq5781 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq512 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq253 X0 x X2
       grind)
    | exact superpose eq253 eq512
    | exact resolve eq512 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq5876 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5781 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5781
    | exact resolve eq5781 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5781
  have eq5886 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5876 X0 x
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq5876
    | exact resolve eq5876 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5876
  have eq6778 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq694 X0 X1 X2 X3
       have i₂ := eq5886 X0
       grind)
    | exact superpose eq5886 eq694
    | exact resolve eq694 eq5886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq6789 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6778 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq253 X0 x x
       grind)
    | exact superpose eq253 eq6778
    | exact resolve eq6778 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6778
  have eq6994 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6789 X0 X1 X2
       have i₂ := eq253 X0 X0 X0
       grind)
    | exact superpose eq253 eq6789
    | exact resolve eq6789 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6789
  have eq7027 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6994 X0 X1 X2
       have i₂ := eq5886 X0
       grind)
    | exact superpose eq5886 eq6994
    | exact resolve eq6994 eq5886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886 eq6994
  have eq7078 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7027 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7027
    | (have j0 := eq7027 y X0 x
       grind)
    | exact resolve eq7027 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7090 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq7027
    | (have j0 := eq7027 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7027 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7360 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq704 X0
       have i₂ := eq7027 X0 X0 X0
       grind)
    | exact superpose eq7027 eq704
    | exact resolve eq704 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq7865 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq79
    | (have j0 := eq79 x
       grind)
    | exact resolve eq79 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq7886 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7865
  have eq7893 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7886
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq7886
    | exact resolve eq7886 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq7886
  have eq7910 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7893
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq7893 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7893
  have eq7915 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq7910 eq49
    | exact resolve eq49 eq7910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq8075 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80
    | (have j0 := eq80 y
       grind)
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq8098 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq8075
  have eq8104 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq8098
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq8098
    | exact resolve eq8098 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq8098
  have eq8128 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq8104
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq8104 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8104
  have eq8151 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8128 eq109
    | exact resolve eq109 eq8128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq8584 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq139
    | (have j0 := eq139 (M.op x y)
       grind)
    | exact resolve eq139 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq8603 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq8584
  have eq8608 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq138 eq8603
    | exact resolve eq8603 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq8603
  have eq8639 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq8608
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8608 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8608
  have eq8676 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq8639 eq172
    | exact resolve eq172 eq8639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq8639
  have eq9922 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 X1
       have i₂ := eq7027 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7027 eq521
    | exact resolve eq521 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq9951 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq9922 X0 x
       grind)
    | exact superpose eq9922 eq52
    | exact resolve eq52 eq9922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9922
  have eq10107 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9951 (M.op X0 (M.op X0 X0))
       have i₂ := eq253 X0 X0 X0
       grind)
    | exact superpose eq253 eq9951
    | exact resolve eq9951 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9951
  have eq10256 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1229 X0
       have i₂ := eq10107 X0
       grind)
    | exact superpose eq10107 eq1229
    | exact resolve eq1229 eq10107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10258 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq10107 X0
       grind)
    | exact superpose eq10107 eq14
    | exact resolve eq14 eq10107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10499 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq7027 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7027 eq522
    | exact resolve eq522 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq10813 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq10499 eq52
    | exact resolve eq52 eq10499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10499
  have eq10983 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq10813 (M.op X0 (M.op X0 X0))
       have i₂ := eq253 X0 X0 X0
       grind)
    | exact superpose eq253 eq10813
    | exact resolve eq10813 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10813
  have eq11421 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq10983 eq14
    | exact resolve eq14 eq10983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10983
  have eq11448 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11421 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq11421
    | exact resolve eq11421 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11421
  have eq12119 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq11448 eq693
    | exact resolve eq693 eq11448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq11448
  have eq12120 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4162 eq12119
    | exact resolve eq12119 eq4162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4162 eq12119
  have eq12121 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7090 eq12120
    | exact resolve eq12120 eq7090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7090 eq12120
  have eq12150 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq12121 (M.op x (M.op x x)) x sF2
       have i₂ := eq52 x x sF2
       grind)
    | exact superpose eq52 eq12121
    | exact resolve eq12121 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12121
  have eq12229 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq706 X0 x
       have i₂ := eq7027 X0 X0 x
       grind)
    | exact superpose eq7027 eq706
    | exact resolve eq706 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq14365 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq519 X0 X1 X2 X3
       have i₂ := eq7027 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq7027 eq519
    | exact resolve eq519 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq14620 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 x X2
       have i₂ := eq14365 X2 X0 X1 x
       grind)
    | exact superpose eq14365 eq52
    | exact resolve eq52 eq14365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq14365
  have eq15207 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq4125 eq14620
    | exact resolve eq14620 eq4125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125
  have eq16244 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op X0 X0) (M.op X0 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq697 X0 X1 X2
       have i₂ := eq7027 X0 X0 y
       grind)
    | exact superpose eq7027 eq697
    | exact resolve eq697 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq16294 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) (M.op (M.op y (M.op x y)) (M.op y (M.op y (M.op x y)))))) := by
    intro X0 X1
    first
    | exact superpose eq242 eq16244
    | exact resolve eq16244 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq16244
  have eq16446 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op y (M.op y (M.op x y))) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3795 eq16294
    | exact resolve eq16294 eq3795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795 eq16294
  have eq16493 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq16446 X0 X1
       have i₂ := eq7027 sF0 y y
       grind)
    | exact superpose eq7027 eq16446
    | exact resolve eq16446 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16446
  have eq16523 : ∀ X0 X1 : G, (M.op y (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op y (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq3966 eq16493
    | exact resolve eq16493 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16493
  have eq20267 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 x
       have i₂ := eq7027 X0 X0 x
       grind)
    | exact superpose eq7027 eq715
    | exact resolve eq715 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq20268 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20267 X0 X1
       have i₂ := eq7360 X0
       grind)
    | exact superpose eq7360 eq20267
    | exact resolve eq20267 eq7360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7360 eq20267
  have eq23588 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq828 x y X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq828
    | (have j0 := eq828 x y x
       grind)
    | exact resolve eq828 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq23705 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23588 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23588
    | (have j0 := eq23588 X0
       grind)
    | exact resolve eq23588 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23588
  have eq23843 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23705 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23705
    | (have j0 := eq23705 X0
       grind)
    | exact resolve eq23705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23705
  have eq23976 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23843 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23843
    | (have j0 := eq23843 X0
       grind)
    | exact resolve eq23843 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23843
  have eq24102 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23976 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23976
    | (have j0 := eq23976 X0
       grind)
    | exact resolve eq23976 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23976
  have eq24186 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq24102 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24102
    | (have j0 := eq24102 X0
       grind)
    | exact resolve eq24102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24102
  have eq24269 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq24186 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24186
    | (have j0 := eq24186 X0
       grind)
    | exact resolve eq24186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24186
  have eq24339 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq24269
    | (have j0 := eq24269 X0
       grind)
    | exact resolve eq24269 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24269
  have eq25663 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq7910 eq91
    | exact resolve eq91 eq7910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq7910
  have eq25677 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25684 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq25677
    | exact resolve eq25677 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25677
  have eq25695 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq25684
       have r₂ := eq27
       grind)
    | exact resolve eq25684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25684
  have eq25697 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq25695
    | exact resolve eq25695 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25695
  have eq25711 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25697 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25697
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25697
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25697
       grind)
    | exact resolve eq13 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25718 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25697 eq117
    | (have r₁ := eq117 (σ x) (σ y)
       have r₂ := eq25697
       grind)
    | (have r₁ := eq117 (σ y) (σ x)
       have r₂ := eq25697
       grind)
    | (have r₁ := eq117 y x
       have r₂ := eq25697
       grind)
    | exact resolve eq117 eq25697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25697
  have eq25741 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq25718
  have eq25742 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq25711
  have eq25753 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq25742
    | exact resolve eq25742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25742
  have eq25761 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq25753
       have r₂ := eq127
       grind)
    | exact resolve eq25753 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25753
  have eq25764 : (k y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25761 eq102
    | exact resolve eq102 eq25761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25761
  have eq25790 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq25764
       grind)
    | exact superpose eq25764 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq25764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25764
  have eq25797 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq25790
  have eq25805 : y = (M.op x y) ∨ (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25797
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25797
    | exact resolve eq25797 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25797
  have eq25806 : (M.op y x) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq25805
  have eq25854 : x = (M.op (M.op x y) (M.op x (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq25806
       grind)
    | exact superpose eq25806 eq50
    | exact resolve eq50 eq25806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq25806
  have eq25905 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25741 eq60
    | exact resolve eq60 eq25741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq25906 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq25741 eq96
    | exact resolve eq96 eq25741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq25741
  have eq25923 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25906
  have eq25931 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq25905
    | exact resolve eq25905 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25905
  have eq25943 : y = (M.op x (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq25923
       grind)
    | exact superpose eq25923 eq53
    | exact resolve eq53 eq25923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25944 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq25923
       grind)
    | exact superpose eq25923 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25923
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25923
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25923
       grind)
    | exact resolve eq13 eq25923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25951 : x ≠ x ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq117 x y
       have i₂ := eq25923
       grind)
    | exact superpose eq25923 eq117
    | (have r₁ := eq117 x y
       have r₂ := eq25923
       grind)
    | (have r₁ := eq117 y x
       have r₂ := eq25923
       grind)
    | (have r₁ := eq117 (σ y) (σ x)
       have r₂ := eq25923
       grind)
    | exact resolve eq117 eq25923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25923
  have eq25974 : x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25951
  have eq25975 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25944
  have eq25986 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25975
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25975
    | exact resolve eq25975 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25975
  have eq25990 : (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25986
       have r₂ := eq126
       grind)
    | exact resolve eq25986 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25986
  have eq25993 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq25990
       grind)
    | exact superpose eq25990 eq75
    | exact resolve eq75 eq25990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26020 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq25993
    | exact resolve eq25993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25993
  have eq26062 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26020 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26069 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq26062
    | exact resolve eq26062 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26062
  have eq26070 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq26069
  have eq27017 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq25974
       grind)
    | exact superpose eq25974 eq44
    | exact resolve eq44 eq25974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq25974
  have eq27044 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27017
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27017
    | exact resolve eq27017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27017
  have eq28868 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq25931
       grind)
    | exact superpose eq25931 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq25931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25931
  have eq28877 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq28868
  have eq28885 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28877
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28877
    | exact resolve eq28877 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28877
  have eq28900 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28885
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28885
    | exact resolve eq28885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28885
  have eq28901 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28900
  have eq28929 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq28901
       grind)
    | exact superpose eq28901 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq28901
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq28901
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq28901
       grind)
    | exact resolve eq13 eq28901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28901
  have eq28962 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28929
  have eq28973 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28962
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28962
    | exact resolve eq28962 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28962
  have eq28977 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28973
       have r₂ := eq126
       grind)
    | exact resolve eq28973 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28973
  have eq29121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq28977
       grind)
    | exact superpose eq28977 eq75
    | exact resolve eq75 eq28977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq29135 : (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq856 y x
       have i₂ := eq28977
       grind)
    | exact superpose eq28977 eq856
    | exact resolve eq856 eq28977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28977
  have eq29137 : (σ x) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29135
    | exact resolve eq29135 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29135
  have eq29150 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29121
    | exact resolve eq29121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29121
  have eq29152 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29137
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29137
    | exact resolve eq29137 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29137
  have eq29160 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29152
    | exact resolve eq29152 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29152
  have eq29166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29160
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29160
    | exact resolve eq29160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29160
  have eq29172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29166
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29166
    | exact resolve eq29166 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29166
  have eq29182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq29172
    | exact resolve eq29172 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29172
  have eq29188 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq29182
       have r₂ := eq27
       grind)
    | exact resolve eq29182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29182
  have eq34938 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26070 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq26070
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq26070
       grind)
    | exact resolve eq13 eq26070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26070
  have eq34975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq34938
  have eq34987 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq34975
    | exact resolve eq34975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34975
  have eq34995 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq34987
       have r₂ := eq127
       grind)
    | exact resolve eq34987 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34987
  have eq35011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34995 eq26020
    | exact resolve eq26020 eq34995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq34995 eq29150
    | exact resolve eq29150 eq34995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29150 eq34995
  have eq35034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq35011
  have eq35043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq35018
       have r₂ := eq29188
       grind)
    | exact resolve eq35018 eq29188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35018
  have eq35048 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq35034
       have r₂ := eq27
       grind)
    | exact resolve eq35034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35034
  have eq35052 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35043
       have r₂ := eq27
       grind)
    | exact resolve eq35043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35043
  have eq35088 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35048 eq12229
    | exact resolve eq12229 eq35048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12229
  have eq35090 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq35048 eq14620
    | exact resolve eq14620 eq35048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14620
  have eq35130 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) X0))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq35052 eq14
    | exact resolve eq14 eq35052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35052
  have eq41079 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq35090 (M.op X0 (M.op X0 X0))
       have i₂ := eq253 X0 X0 X0
       grind)
    | exact superpose eq253 eq35090
    | exact resolve eq35090 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq35090
  have eq42327 : (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35130 eq707
    | exact resolve eq707 eq35130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq35130
  have eq42417 : (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42327
       have i₂ := eq7027 sF1 sF1 sF2
       grind)
    | exact superpose eq7027 eq42327
    | exact resolve eq42327 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42327
  have eq42448 : (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42417
       have i₂ := eq20268 sF1 sF2
       grind)
    | exact superpose eq20268 eq42417
    | exact resolve eq42417 eq20268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20268 eq42417
  have eq42463 : (M.op y (M.op (M.op x y) (σ (M.op x y)))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq42448
       have i₂ := eq10107 sF1
       grind)
    | exact superpose eq10107 eq42448
    | exact resolve eq42448 eq10107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10107 eq42448
  have eq51660 : ∀ X0 : G, (k (σ X0) (σ (M.op x y))) = (σ (k X0 (k y x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26020 eq100
    | exact resolve eq100 eq26020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq51687 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (k X0 (k y x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq41 eq51660
    | exact resolve eq51660 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq51660
  have eq51807 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (k (k y x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26020 eq101
    | exact resolve eq101 eq26020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq26020
  have eq51945 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (k (k y x) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq51807
    | exact resolve eq51807 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq51807
  have eq52063 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8128 eq110
    | exact resolve eq110 eq8128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq8128
  have eq54096 : ∀ X0 : G, (k X0 (k y x)) = (τ (σ (k X0 (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 (k y x))
       have i₂ := eq51687 X0
       grind)
    | exact superpose eq51687 eq16
    | exact resolve eq16 eq51687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51687
  have eq54181 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k y x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54096 X0
       have i₂ := eq16 (k X0 sF0)
       grind)
    | exact superpose eq16 eq54096
    | exact resolve eq54096 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54096
  have eq54462 : ∀ X0 : G, (k (k y x) X0) = (τ (σ (k (M.op x y) X0))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 (k (k y x) X0)
       have i₂ := eq51945 X0
       grind)
    | exact superpose eq51945 eq16
    | exact resolve eq16 eq51945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51945
  have eq54551 : ∀ X0 : G, (k (M.op x y) X0) = (k (k y x) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq54462 X0
       have i₂ := eq16 (k sF0 X0)
       grind)
    | exact superpose eq16 eq54462
    | exact resolve eq54462 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54462
  have eq54635 : (k (M.op x y) (k y x)) = (k (k y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54181 (k y x)
       have i₂ := eq54551 (k y x)
       grind)
    | exact superpose eq54551 eq54181
    | exact resolve eq54181 eq54551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54181 eq54551
  have eq54646 : (k (M.op x y) (k y x)) = (k (k y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54635
  have eq56121 : (k (M.op x y) (k y x)) = (M.op (k y x) (M.op x y)) ∨ (k y x) = (M.op (M.op x y) (k y x)) ∨ (M.op x y) = (M.op (k y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54646 eq11
    | (have j0 := eq11 (k y x) (M.op x y)
       grind)
    | exact resolve eq11 eq54646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54646
  have eq56156 : (k (M.op x y) (k y x)) = (M.op (k y x) (M.op x y)) ∨ (M.op x y) = (M.op (k y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq56121
       have r₂ := eq13 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq56121
       have r₂ := eq13 (k y x) (M.op x y)
       grind)
    | (have r₁ := eq56121
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq56121 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56121
  have eq56170 : (k (M.op x y) (k y x)) = (M.op (k y x) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq117 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq56156
       have r₂ := eq117 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq56156
       have r₂ := eq117 (σ y) (σ x)
       grind)
    | exact resolve eq56156 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56156
  have eq66560 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56170
       have i₂ := eq25990
       grind)
    | exact superpose eq25990 eq56170
    | exact resolve eq56170 eq25990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25990 eq56170
  have eq66606 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq66560
  have eq66625 : (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3966 eq66606
    | exact resolve eq66606 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66606
  have eq80985 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op X1 (σ x)) (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (M.op X0 X0)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f80985_15 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      grind
    have f80985_21 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
      intro X0 X1 X2
      grind
    have f80985_24 : (M.op (σ (M.op x y)) X0) ≠ (M.op (M.op X1 (σ x)) (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (M.op X0 X0)))) := by grind
    have f80985_25 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f80985_26 : (σ x) ≠ (σ (M.op x y)) := by grind
    have f80985_28 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (σ (M.op x y)) := by
      intro X0
      first
      | (have j0 := f80985_15 X0
         grind)
      | (have r₁ := f80985_15 X0
         have r₂ := f80985_25
         grind)
      | exact resolve f80985_15 f80985_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f80985_29 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
      intro X0
      first
      | (have j0 := f80985_28 X0
         grind)
      | (have r₁ := f80985_28 X0
         have r₂ := f80985_26
         grind)
      | exact resolve f80985_28 f80985_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f80985_73 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op X1 (σ x)) (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (M.op X0 X0)))) := by
      intro X0 X1
      first
      | (have i₁ := f80985_21 (M.op (σ (M.op x y)) X0) X1 (σ x)
         have i₂ := f80985_29 X0
         grind)
      | exact superpose f80985_29 f80985_21
      | exact resolve f80985_21 f80985_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f80985_75 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op X1 (σ x)) X0) := by
      intro X0 X1
      first
      | (have i₁ := f80985_73 X0 X1
         have i₂ := f80985_21 X0 (σ (M.op x y)) X0
         grind)
      | exact superpose f80985_21 f80985_73
      | exact resolve f80985_73 f80985_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f80985_107 : (M.op (σ (M.op x y)) X0) ≠ (M.op (M.op X1 (σ x)) X0) := by
      first
      | (have i₁ := f80985_24
         have i₂ := f80985_21 X0 (σ (M.op x y)) X0
         grind)
      | exact superpose f80985_21 f80985_24
      | exact resolve f80985_24 f80985_21
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f80985_108 : False := by
      first
      | (have r₁ := f80985_107
         have r₂ := f80985_75 X0 X1
         grind)
      | exact resolve f80985_107 f80985_75
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f80985_108
  clear eq41079
  have eq81083 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (M.op X1 (σ x)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq80985 X0 X1
       have i₂ := eq14 X0 sF1 X0
       grind)
    | exact superpose eq14 eq80985
    | exact resolve eq80985 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80985
  have eq396998 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq81083 eq35088
    | exact resolve eq35088 eq81083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35088 eq81083
  have eq397110 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq396998
  have eq398409 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42463 eq397110
    | exact resolve eq397110 eq42463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42463 eq397110
  have eq398525 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq398409
  have eq398601 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op y (M.op (M.op x y) (σ (M.op x y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq398525
       have r₂ := eq29188
       grind)
    | exact resolve eq398525 eq29188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29188 eq398525
  have eq486476 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35048 eq24339
    | exact resolve eq24339 eq35048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24339
  have eq486611 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (k (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq486476
  have eq486771 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27044 eq486611
    | exact resolve eq486611 eq27044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27044 eq486611
  have eq486895 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq486771
  have eq489111 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35048 eq486895
    | exact resolve eq486895 eq35048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35048 eq486895
  have eq489270 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq489111
  have eq489409 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq489270 eq8676
    | exact resolve eq8676 eq489270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8676 eq489270
  have eq490003 : y = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq489409
    | exact resolve eq489409 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489409
  have eq497134 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq490003 eq66625
    | exact resolve eq66625 eq490003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66625 eq490003
  have eq497280 : y = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq497134
  have eq502129 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq497280 eq25943
    | exact resolve eq25943 eq497280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25943 eq497280
  have eq502479 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq502129
  have eq502653 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq502479
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq502479
    | exact resolve eq502479 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502479
  have eq502654 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq502653
  have eq502820 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq502654 eq127
    | (have r₁ := eq127
       have r₂ := eq502654
       grind)
    | exact resolve eq127 eq502654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq502897 : x = (M.op (M.op x y) (M.op x (τ (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq502654 eq25854
    | exact resolve eq25854 eq502654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25854 eq502654
  have eq503107 : x = (M.op (M.op x y) (M.op x (τ (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq502897
  have eq503109 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq502820
  have eq503152 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq503107
    | exact resolve eq503107 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503107
  have eq503190 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq503152
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq503152
    | exact resolve eq503152 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503152
  have eq503198 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3966 eq503190
    | exact resolve eq503190 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503190
  have eq503597 : (τ (σ y)) = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq503109 eq102
    | exact resolve eq102 eq503109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq503109
  have eq503890 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq503597
    | exact resolve eq503597 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq503597
  have eq504346 : x ≠ y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5185 y x
       have i₂ := eq503890
       grind)
    | exact superpose eq503890 eq5185
    | exact resolve eq5185 eq503890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5185
  have eq504436 : y = (M.op x y) ∨ x ≠ y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq504346
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq504346
    | exact resolve eq504346 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504346
  have eq504437 : x ≠ y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq504436
  have eq594494 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq4547 X0
       have i₂ := eq7027 (M.op X0 sF0) (M.op X0 sF0) (M.op X0 sF0)
       grind)
    | exact superpose eq7027 eq4547
    | exact resolve eq4547 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547 eq7027
  have eq687471 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq503198 eq53
    | exact resolve eq53 eq503198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503198
  have eq687939 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq687471 x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq687471
    | exact resolve eq687471 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687471
  have eq713582 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1229 x
       have i₂ := eq687939
       grind)
    | exact superpose eq687939 eq1229
    | exact resolve eq1229 eq687939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229 eq687939
  have eq714034 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq713582
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq713582
    | exact resolve eq713582 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713582
  have eq718920 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq714034
       grind)
    | exact superpose eq714034 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq714034
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq714034
       grind)
    | exact resolve eq13 eq714034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714034
  have eq719030 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq718920
  have eq719076 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq719030
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq719030
    | exact resolve eq719030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719030
  have eq719097 : (M.op x y) = (k y x) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq719076
       have r₂ := eq126
       grind)
    | exact resolve eq719076 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq719076
  have eq719203 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq503890
       have i₂ := eq719097
       grind)
    | exact superpose eq719097 eq503890
    | exact resolve eq503890 eq719097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503890 eq719097
  have eq719232 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq719203
  have eq719802 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719232 eq7078
    | exact resolve eq7078 eq719232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7078
  have eq719807 : ∀ X0 : G, (M.op (M.op X0 x) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq719232 eq16523
    | exact resolve eq16523 eq719232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16523
  have eq719819 : (M.op y x) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719232 eq594494
    | exact resolve eq594494 eq719232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594494
  have eq719826 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719232 eq56
    | exact resolve eq56 eq719232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720009 : (M.op y (M.op x y)) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3966 eq719826
    | exact resolve eq719826 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966 eq719826
  have eq720012 : y = (M.op y (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53 eq719807
    | exact resolve eq719807 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719807
  have eq720014 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq719802
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq719802
    | exact resolve eq719802 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719802
  have eq720080 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52063
       have i₂ := eq720014
       grind)
    | exact superpose eq720014 eq52063
    | exact resolve eq52063 eq720014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720014
  have eq720426 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq720080
  have eq720531 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq720426
    | exact resolve eq720426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720426
  have eq722445 : y = (M.op y (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq720009 eq720012
    | exact resolve eq720012 eq720009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720009 eq720012
  have eq722641 : y = (M.op y (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq722445
  have eq728203 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719232 eq722641
    | exact resolve eq722641 eq719232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719232 eq722641
  have eq728349 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq728203
  have eq728617 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq719819
       have i₂ := eq728349
       grind)
    | exact superpose eq728349 eq719819
    | exact resolve eq719819 eq728349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719819 eq728349
  have eq728747 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq728617
  have eq728966 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq25663
       have i₂ := eq728747
       grind)
    | exact superpose eq728747 eq25663
    | exact resolve eq25663 eq728747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25663 eq728747
  have eq729450 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq728966
       have r₂ := eq504437
       grind)
    | exact resolve eq728966 eq504437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504437 eq728966
  have eq729513 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq729450
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq729450
    | exact resolve eq729450 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729450
  have eq730655 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq729513 eq15207
    | exact resolve eq15207 eq729513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15207 eq729513
  have eq730836 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12150 eq730655
    | exact resolve eq730655 eq12150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12150 eq730655
  have eq731833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq730836 eq720531
    | exact resolve eq720531 eq730836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720531 eq730836
  have eq732196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq731833
  have eq732345 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq732196
       have r₂ := eq27
       grind)
    | exact resolve eq732196 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732196
  have eq732734 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq732345 eq28
    | exact resolve eq28 eq732345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq732345
  have eq733371 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq732734
    | exact resolve eq732734 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732734
  have eq733376 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq733371 eq20
    | exact resolve eq20 eq733371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq733894 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq733371
  have eq734158 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq733376
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq733376
    | exact resolve eq733376 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733376
  have eq734831 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq734158 eq398601
    | exact resolve eq398601 eq734158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398601 eq734158
  have eq735023 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ (M.op x y))))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq734831
  have eq735201 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (M.op y (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq735023
       have r₂ := eq27
       grind)
    | exact resolve eq735023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735023
  have eq735513 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10256 eq735201
    | exact resolve eq735201 eq10256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10256 eq735201
  have eq738378 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq735513 eq7915
    | exact resolve eq7915 eq735513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915 eq735513
  have eq738933 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq738378
    | exact resolve eq738378 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738378
  have eq740271 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq738933
       grind)
    | exact superpose eq738933 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq738933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740295 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq740271
  have eq2634064 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq740295
       grind)
    | exact superpose eq740295 eq56
    | exact resolve eq56 eq740295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740295
  have eq2765239 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2634064 eq10258
    | exact resolve eq10258 eq2634064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10258 eq2634064
  have eq2765595 : x = y ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53 eq2765239
    | exact resolve eq2765239 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2765239
  have eq2765639 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2765595
       have r₂ := eq733894
       grind)
    | exact resolve eq2765595 eq733894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733894 eq2765595
  have eq2766004 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq117 x x
       have i₂ := eq2765639
       grind)
    | exact superpose eq2765639 eq117
    | (have r₁ := eq117 x x
       have r₂ := eq2765639
       grind)
    | exact resolve eq117 eq2765639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq2765639
  have eq2766205 : x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq2766004
  have eq2766522 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq738933
       have i₂ := eq2766205
       grind)
    | exact superpose eq2766205 eq738933
    | exact resolve eq738933 eq2766205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738933 eq2766205
  have eq2766651 : x = (M.op x y) := by grind
  clear eq2766522
  have eq2766854 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2766651 eq20
    | exact resolve eq20 eq2766651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2766905 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2766651 eq215
    | exact resolve eq215 eq2766651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq2767726 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2766905
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2766905
    | exact resolve eq2766905 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2766905
  have eq2767771 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2766854
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2766854
    | exact resolve eq2766854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766854
  have eq2767789 : x = (M.op y y) := by
    first
    | exact superpose eq2766651 eq2767726
    | exact resolve eq2767726 eq2766651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767726
  have eq2768705 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2767771 eq26
    | exact resolve eq26 eq2767771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2770115 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq52063
       have i₂ := eq2767789
       grind)
    | exact superpose eq2767789 eq52063
    | exact resolve eq52063 eq2767789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52063
  have eq2770541 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2767789
       grind)
    | exact superpose eq2767789 eq13
    | exact resolve eq13 eq2767789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767789
  have eq2771065 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2770115
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2770115
    | exact resolve eq2770115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770115
  have eq2771241 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2767771 eq2771065
    | exact resolve eq2771065 eq2767771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771065
  have eq2790734 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq2771241 eq8151
    | exact resolve eq8151 eq2771241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8151
  have eq2791254 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2771241 eq56
    | exact resolve eq56 eq2771241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq2771241
  have eq2791596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2768705 eq2791254
    | exact resolve eq2791254 eq2768705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791254
  have eq2791809 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq30 eq2790734
    | exact resolve eq2790734 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2790734
  have eq2791870 : x = y := by
    first
    | (have r₁ := eq2791596
       have r₂ := eq27
       grind)
    | exact resolve eq2791596 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791596
  have eq2791969 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq2766651 eq2791809
    | exact resolve eq2791809 eq2766651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766651 eq2791809
  have eq2792033 : x = (k y y) := by
    first
    | (have r₁ := eq2791969
       have r₂ := eq2770541
       grind)
    | exact resolve eq2791969 eq2770541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2770541 eq2791969
  have eq2792097 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2791870
       grind)
    | exact superpose eq2791870 eq24
    | exact resolve eq24 eq2791870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2794026 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2792097
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2792097
    | exact resolve eq2792097 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792097
  have eq2794323 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2767771 eq2794026
    | exact resolve eq2794026 eq2767771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794026
  have eq2795999 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2794323 eq2768705
    | exact resolve eq2768705 eq2794323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768705 eq2794323
  have eq2796790 : x = (k x x) := by
    first
    | (have i₁ := eq2792033
       have i₂ := eq2791870
       grind)
    | exact superpose eq2791870 eq2792033
    | exact resolve eq2792033 eq2791870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2791870 eq2792033
  have eq2796893 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq856 x x
       have i₂ := eq2796790
       grind)
    | exact superpose eq2796790 eq856
    | exact resolve eq856 eq2796790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq2796790
  have eq2796913 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2796893
  have eq2796942 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2796913
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2796913
    | exact resolve eq2796913 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2796913
  have eq2797019 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2767771 eq2796942
    | exact resolve eq2796942 eq2767771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2767771 eq2796942
  have eq2800517 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2797019 eq2795999
    | exact resolve eq2795999 eq2797019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795999 eq2797019
  have eq2800518 : False := by grind
  exact eq2800518

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pxy_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq10
    | exact resolve eq10 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq70 sF2
       grind)
    | exact superpose eq70 eq50
    | exact resolve eq50 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq75 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq74
       have i₂ := eq70 x
       grind)
    | exact superpose eq70 eq74
    | exact resolve eq74 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq72
    | exact resolve eq72 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq106 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq107 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq111 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq70 sF3
       grind)
    | exact superpose eq70 eq107
    | exact resolve eq107 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq70 y
       grind)
    | exact superpose eq70 eq111
    | exact resolve eq111 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq111
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq106
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq115
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq115
    | exact resolve eq115 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq122
    | exact resolve eq122 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq151 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq16
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq271 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq57 X0 X2
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0) (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq57
    | exact resolve eq57 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq664 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq53 X2 X3 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq53 y X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq673 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq53 sF3 x x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq784 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op (M.op X3 (M.op X4 (M.op X2 X1))) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X0 (M.op X2 X0)) X1 X2 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq788 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq6403 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq664 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq271 X0 x X2
       grind)
    | exact superpose eq271 eq664
    | exact resolve eq664 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6499 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq6403 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq6403
    | exact resolve eq6403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403
  have eq6513 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6499 X0 x
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq6499
    | exact resolve eq6499 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6499
  have eq7425 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq788 X0 X1 X2 X3
       have i₂ := eq6513 X0
       grind)
    | exact superpose eq6513 eq788
    | exact resolve eq788 eq6513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq7440 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7425 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq271 X0 x x
       grind)
    | exact superpose eq271 eq7425
    | exact resolve eq7425 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7425
  have eq7686 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7440 X0 X1 X2
       have i₂ := eq271 X0 X0 X0
       grind)
    | exact superpose eq271 eq7440
    | exact resolve eq7440 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7440
  have eq7724 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7686 X0 X1 X2
       have i₂ := eq6513 X0
       grind)
    | exact superpose eq6513 eq7686
    | exact resolve eq7686 eq6513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6513 eq7686
  have eq8915 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq672 X0 X1
       have i₂ := eq7724 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7724 eq672
    | exact resolve eq672 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq9039 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y x X0
       have i₂ := eq8915 X0 x
       grind)
    | exact superpose eq8915 eq53
    | exact resolve eq53 eq8915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq9183 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq9039 (M.op X0 (M.op X0 X0))
       have i₂ := eq271 X0 X0 X0
       grind)
    | exact superpose eq271 eq9039
    | exact resolve eq9039 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9318 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq9183 X0
       grind)
    | exact superpose eq9183 eq14
    | exact resolve eq14 eq9183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9549 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq673 X0 X1
       have i₂ := eq7724 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7724 eq673
    | exact resolve eq673 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq9817 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9549 eq53
    | exact resolve eq53 eq9549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9549
  have eq9978 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9817 (M.op X0 (M.op X0 X0))
       have i₂ := eq271 X0 X0 X0
       grind)
    | exact superpose eq271 eq9817
    | exact resolve eq9817 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9817
  have eq10493 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9978 X0
       have i₂ := eq9183 X0
       grind)
    | exact superpose eq9183 eq9978
    | exact resolve eq9978 eq9183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9183 eq9978
  have eq13509 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) X0))) = (M.op y (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10493 (M.op (M.op X0 (M.op (M.op x sF4) X0)) X0)
       have i₂ := eq664 X0 sF4 x
       grind)
    | exact superpose eq664 eq10493
    | exact resolve eq10493 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq10493
  have eq13603 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13509 X0 X1
       have i₂ := eq7724 X0 X0 (M.op X1 sF4)
       grind)
    | exact superpose eq7724 eq13509
    | exact resolve eq13509 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13509
  have eq13615 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op (σ x) (σ y))) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq9039 eq13603
    | exact resolve eq13603 eq9039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9039 eq13603
  have eq16365 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq670 X0 X1 X2 X3
       have i₂ := eq7724 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq7724 eq670
    | exact resolve eq670 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq16797 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x X2
       have i₂ := eq16365 X2 X0 X1 x
       grind)
    | exact superpose eq16365 eq53
    | exact resolve eq53 eq16365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq16365
  have eq17475 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16797 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq271 X0 X0 X0
       grind)
    | exact superpose eq271 eq16797
    | exact resolve eq16797 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq16797
  have eq24874 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X2 X1))) (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq784 X0 X2 X2 X3 X4
       have i₂ := eq7724 X0 X0 X2
       grind)
    | exact superpose eq7724 eq784
    | exact resolve eq784 eq7724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq7724
  have eq25508 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X0))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24874 X0 X0 X3 X1 X2
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq24874
    | exact resolve eq24874 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24874
  have eq101089 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op (σ x) (σ y)))) X0) = (M.op (σ y) (M.op (M.op (M.op X1 (M.op X2 (M.op (σ x) (σ y)))) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13615 (M.op (M.op X2 (M.op X1 sF4)) X0) X1
       have i₂ := eq17475 X0 (M.op X1 sF4) X2
       grind)
    | exact superpose eq17475 eq13615
    | exact resolve eq13615 eq17475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13615 eq17475
  have eq101191 : ∀ X0 X1 X2 : G, (M.op (σ y) X0) = (M.op (M.op X1 (M.op X2 (M.op (σ x) (σ y)))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101089 X0 X1 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X2 sF4)) X0
       grind)
    | exact superpose eq14 eq101089
    | exact resolve eq101089 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101089
  have eq124450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq124450
    | exact resolve eq124450 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124450
  have eq124471 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq124460
       have r₂ := eq28
       grind)
    | exact resolve eq124460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124460
  have eq124475 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq124471
    | exact resolve eq124471 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124471
  have eq124479 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq124475 eq68
    | (have r₁ := eq68
       have r₂ := eq124475
       grind)
    | exact resolve eq68 eq124475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq124624 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq124475 eq25508
    | exact resolve eq25508 eq124475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25508 eq124475
  have eq124656 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq124479
  have eq124674 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq101191 eq124624
    | exact resolve eq124624 eq101191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101191 eq124624
  have eq128356 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq124656 eq123
    | exact resolve eq123 eq124656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq124656
  have eq128373 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq128356
  have eq128383 : (τ (σ x)) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq128373 eq151
    | exact resolve eq151 eq128373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128373
  have eq128635 : x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq29 eq128383
    | exact resolve eq128383 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128383
  have eq128636 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq128635
  have eq129003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq128636 eq124674
    | exact resolve eq124674 eq128636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124674 eq128636
  have eq129072 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq129003
  have eq129096 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq129072
       have r₂ := eq28
       grind)
    | exact resolve eq129072 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129072
  have eq129103 : (τ (σ x)) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq129096 eq151
    | exact resolve eq151 eq129096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq129096
  have eq129355 : x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq129103
    | exact resolve eq129103 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq129103
  have eq129356 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq129355
  have eq129511 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq57 x x
       have i₂ := eq129356
       grind)
    | exact superpose eq129356 eq57
    | exact resolve eq57 eq129356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129356
  have eq130159 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq129511 eq9318
    | exact resolve eq9318 eq129511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9318 eq129511
  have eq130264 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq54 eq130159
    | exact resolve eq130159 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq130159
  have eq130334 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq520 y
       have i₂ := eq130264
       grind)
    | exact superpose eq130264 eq520
    | exact resolve eq520 eq130264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq130433 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq57 y y
       have i₂ := eq130264
       grind)
    | exact superpose eq130264 eq57
    | exact resolve eq57 eq130264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq130264
  have eq130507 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq130433
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq130433
    | exact resolve eq130433 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130433
  have eq130544 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq130334
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq130334
    | exact resolve eq130334 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130334
  have eq130573 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq130544
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq130544
    | exact resolve eq130544 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130544
  have eq130581 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq130573
    | exact resolve eq130573 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130573
  have eq130583 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq130507 eq21
    | exact resolve eq21 eq130507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130507
  have eq130853 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq130583
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq130583
    | exact resolve eq130583 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130583
  have eq130882 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq130581 eq28
    | exact resolve eq28 eq130581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130581
  have eq131220 : x = y := by
    first
    | (have r₁ := eq130882
       have r₂ := eq130853
       grind)
    | exact resolve eq130882 eq130853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130853 eq130882
  have eq131221 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq131220
       grind)
    | exact superpose eq131220 eq19
    | exact resolve eq19 eq131220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq131222 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq131220
       grind)
    | exact superpose eq131220 eq25
    | exact resolve eq25 eq131220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq131220
  have eq131509 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq131222
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131222
    | exact resolve eq131222 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq131222
  have eq131560 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq131509 eq27
    | exact resolve eq27 eq131509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq131509
  have eq132345 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq131560 eq75
    | exact resolve eq75 eq131560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq131560
  have eq132626 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq132345
       have i₂ := eq131221
       grind)
    | exact superpose eq131221 eq132345
    | exact resolve eq132345 eq131221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131221 eq132345
  have eq132756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132626 eq15
    | exact resolve eq15 eq132626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132626
  have eq132863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq132756
    | exact resolve eq132756 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq132756
  have eq132900 : False := by grind
  exact eq132900

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_y_pyx_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq45
    | (have j0 := eq45 (σ X0) (σ X1)
       grind)
    | exact resolve eq45 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq36 (τ X0)
       grind)
    | exact superpose eq36 eq19
    | exact resolve eq19 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq90 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq90
    | exact resolve eq90 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq90
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq174 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq26
    | exact resolve eq26 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq858 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq148
       have i₂ := eq102 y
       grind)
    | exact superpose eq102 eq148
    | exact resolve eq148 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq148
  have eq859 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq858
       have i₂ := eq45 y x
       grind)
    | exact superpose eq45 eq858
    | (have j1 := eq45 y x
       grind)
    | exact resolve eq858 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq858
  have eq862 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq859
  have eq865 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq862
       grind)
    | exact superpose eq862 eq174
    | exact resolve eq174 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26 y y
       have i₂ := eq862
       grind)
    | exact superpose eq862 eq26
    | exact resolve eq26 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq3930 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq865
       grind)
    | exact superpose eq865 eq16
    | exact resolve eq16 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq3962 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3930
       have i₂ := eq878
       grind)
    | exact superpose eq878 eq3930
    | exact resolve eq3930 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq3930
  have eq3963 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq3962
  have eq3964 : (σ x) = (σ (M.op y y)) := by grind
  clear eq3963
  have eq3966 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq3964
       grind)
    | exact superpose eq3964 eq174
    | exact resolve eq174 eq3964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq3976 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3964
       grind)
    | exact superpose eq3964 eq10
    | exact resolve eq10 eq3964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq4022 : x = (M.op y y) := by
    first
    | (have i₁ := eq3976
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3976
    | exact resolve eq3976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq4063 : x = (M.op x y) := by
    first
    | (have i₁ := eq26 y y
       have i₂ := eq4022
       grind)
    | exact superpose eq4022 eq26
    | exact resolve eq26 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4022
  have eq4348 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3966
       grind)
    | exact superpose eq3966 eq16
    | exact resolve eq16 eq3966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3966
  have eq4379 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4348
       have i₂ := eq4063
       grind)
    | exact superpose eq4063 eq4348
    | exact resolve eq4348 eq4063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4063 eq4348
  have eq4380 : False := by grind
  exact eq4380

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_x_pxy_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq16
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) (M.op X1 X2)) ≠ X0 ∨ (M.op X1 X2) = X0 ∨ (k (M.op X0 (M.op X2 X0)) (M.op X1 X2)) = (M.op (M.op X0 (M.op X2 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X2 X0)) (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 (M.op X2 X0)) (M.op X1 X2)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq150 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq193 : (σ (k (k y x) (M.op x y))) = (k (k (σ y) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq41
    | exact resolve eq41 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq204 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y y))) := by
    intro X0
    first
    | exact superpose eq204 eq14
    | exact resolve eq14 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X0 (M.op X1 X0)) (M.op x X1)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq244 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq62 X0 X2
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq62 X0 X0
       grind)
    | exact resolve eq13 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq58 X2 X3 X0
       grind)
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq507 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq58 y X1 X0
       grind)
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq58 sF3 x x
       grind)
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq582 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq60 eq61
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq590 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq60 eq61
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq591 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq61
    | exact resolve eq61 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq62 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq62 eq61
    | exact resolve eq61 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X1 x (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq61 X0 X1 x X1
       grind)
    | exact superpose eq61 eq58
    | exact resolve eq58 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq774 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq70 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq785 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq774 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq786 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq785 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq791 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq786
    | (have j0 := eq786 X0 X1
       grind)
    | exact resolve eq786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq792 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq791 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq884 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X0 (M.op X2 X0)) X1)) X0) ≠ X1 ∨ X0 = X1 ∨ (M.op (M.op X1 (M.op (M.op X0 (M.op X2 X0)) X1)) X0) = (k (M.op X1 (M.op (M.op X0 (M.op X2 X0)) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (M.op X1 X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq100
    | (have j0 := eq100 (k (M.op X1 (M.op (M.op X0 (M.op X2 X0)) X1)) X0) (M.op X1 (M.op (M.op X0 (M.op X2 X0)) X1)) X0
       grind)
    | exact resolve eq100 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1334 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq244 X0 x x
       grind)
    | exact superpose eq244 eq62
    | exact resolve eq62 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1342 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1334 X0
       have i₂ := eq244 X0 X0 X0
       grind)
    | exact superpose eq244 eq1334
    | exact resolve eq1334 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1481 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq246 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq3786 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq581 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1342 sF0
       grind)
    | exact superpose eq1342 eq581
    | exact resolve eq581 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3817 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3786
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3786
    | exact resolve eq3786 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3786
  have eq3823 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3817 eq581
    | exact resolve eq581 eq3817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq3855 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3823 eq14
    | exact resolve eq14 eq3823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823
  have eq3891 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq582 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1342 sF4
       grind)
    | exact superpose eq1342 eq582
    | exact resolve eq582 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3922 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3891
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3891
    | exact resolve eq3891 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3891
  have eq3947 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3922 eq582
    | exact resolve eq582 eq3922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq3979 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3947 eq14
    | exact resolve eq14 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4054 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3855 eq56
    | exact resolve eq56 eq3855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3855
  have eq4095 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq4054 eq1481
    | exact resolve eq1481 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4100 : (M.op y (M.op x y)) ≠ (M.op y (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4054 eq12
    | exact resolve eq12 eq4054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4116 : (M.op y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq4100
  have eq4196 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3979 eq57
    | exact resolve eq57 eq3979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq3979
  have eq4232 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4196 eq3947
    | exact resolve eq3947 eq4196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3947
  have eq5605 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq792
    | (have j0 := eq792 (M.op x y) X0
       grind)
    | exact resolve eq792 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5707 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X1)
       have i₂ := eq792 X1 X0
       grind)
    | exact superpose eq792 eq62
    | (have j1 := eq792 X1 X0
       grind)
    | exact resolve eq62 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq6720 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq499 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq244 X0 x X2
       grind)
    | exact superpose eq244 eq499
    | exact resolve eq499 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6817 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq6720 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq6720
    | exact resolve eq6720 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6720
  have eq6827 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6817 X0 x
       have i₂ := eq62 X0 x
       grind)
    | exact superpose eq62 eq6817
    | exact resolve eq6817 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6817
  have eq7442 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq591 X0 X1 X2 X3
       have i₂ := eq6827 X0
       grind)
    | exact superpose eq6827 eq591
    | exact resolve eq591 eq6827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq7453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7442 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq244 X0 x x
       grind)
    | exact superpose eq244 eq7442
    | exact resolve eq7442 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7668 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7453 X0 X1 X2
       have i₂ := eq244 X0 X0 X0
       grind)
    | exact superpose eq244 eq7453
    | exact resolve eq7453 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7453
  have eq7701 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7668 X0 X1 X2
       have i₂ := eq6827 X0
       grind)
    | exact superpose eq6827 eq7668
    | exact resolve eq7668 eq6827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827 eq7668
  have eq7756 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7701 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7701
    | (have j0 := eq7701 y X0 x
       grind)
    | exact resolve eq7701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7768 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq7701
    | (have j0 := eq7701 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7840 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq7701 X0 X0 sF0
       grind)
    | exact superpose eq7701 eq581
    | exact resolve eq581 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq7842 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq7701 X0 X0 sF4
       grind)
    | exact superpose eq7701 eq582
    | exact resolve eq582 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq8059 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq600 X0
       have i₂ := eq7701 X0 X0 X0
       grind)
    | exact superpose eq7701 eq600
    | exact resolve eq600 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq8083 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq244 (M.op X0 X0) X1 X2
       have i₂ := eq8059 X0
       grind)
    | exact superpose eq8059 eq244
    | exact resolve eq244 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059
  have eq8122 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8083 X0 X1 X2
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq8083
    | exact resolve eq8083 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8083
  have eq8476 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq507 X0 X1
       have i₂ := eq7701 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7701 eq507
    | exact resolve eq507 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq8677 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 y x X0
       have i₂ := eq8476 X0 x
       grind)
    | exact superpose eq8476 eq58
    | exact resolve eq58 eq8476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8814 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8677 (M.op X0 (M.op X0 X0))
       have i₂ := eq244 X0 X0 X0
       grind)
    | exact superpose eq244 eq8677
    | exact resolve eq8677 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8677
  have eq8954 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1342 X0
       have i₂ := eq8814 X0
       grind)
    | exact superpose eq8814 eq1342
    | exact resolve eq1342 eq8814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq8976 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7842 sF4
       have i₂ := eq8814 sF4
       grind)
    | exact superpose eq8814 eq7842
    | exact resolve eq7842 eq8814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7842 eq8814
  have eq9108 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4196 eq8976
    | exact resolve eq8976 eq4196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196 eq8976
  have eq9187 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq508 X0 X1
       have i₂ := eq7701 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7701 eq508
    | exact resolve eq508 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq9479 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9187 eq58
    | exact resolve eq58 eq9187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9187
  have eq9630 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9479 (M.op X0 (M.op X0 X0))
       have i₂ := eq244 X0 X0 X0
       grind)
    | exact superpose eq244 eq9479
    | exact resolve eq9479 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq9479
  have eq10050 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9630 eq14
    | exact resolve eq14 eq9630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9630
  have eq10078 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10050 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq10050
    | exact resolve eq10050 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10050
  have eq10723 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq10078 eq590
    | exact resolve eq590 eq10078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq10078
  have eq10724 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4232 eq10723
    | exact resolve eq10723 eq4232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232 eq10723
  have eq10725 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7768 eq10724
    | exact resolve eq10724 eq7768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7768 eq10724
  have eq10753 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq10725 (M.op x (M.op x x)) x sF2
       have i₂ := eq58 x x sF2
       grind)
    | exact superpose eq58 eq10725
    | exact resolve eq10725 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq10725
  have eq10838 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 x
       have i₂ := eq7701 X0 X0 x
       grind)
    | exact superpose eq7701 eq602
    | exact resolve eq602 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq10948 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10838 (M.op X0 (M.op X1 X0)) (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq10838
    | exact resolve eq10838 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10838
  have eq11233 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10948 X0 X1 X2
       have i₂ := eq7701 X0 X0 X1
       grind)
    | exact superpose eq7701 eq10948
    | exact resolve eq10948 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10948
  have eq11339 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11233 X0 X1 X2
       have i₂ := eq7442 X0 X1 (M.op X0 (M.op X1 X0)) X0
       grind)
    | exact superpose eq7442 eq11233
    | exact resolve eq11233 eq7442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7442 eq11233
  have eq11398 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11339 X0 X1 X2
       have i₂ := eq232 X0 X1
       grind)
    | exact superpose eq232 eq11339
    | exact resolve eq11339 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq11339
  have eq12643 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq9108 eq10753
    | exact resolve eq10753 eq9108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9108 eq10753
  have eq14747 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq505 X0 X1 X2 X3
       have i₂ := eq7701 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq7701 eq505
    | exact resolve eq505 eq7701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq7701
  have eq15048 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = (M.op X1 (M.op (M.op X2 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq499 X1 X1 X2
       have i₂ := eq14747 X1 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14747 eq499
    | exact resolve eq499 eq14747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq14747
  have eq15252 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15048 X0 X1 x
       have i₂ := eq62 X1 x
       grind)
    | exact superpose eq62 eq15048
    | exact resolve eq15048 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq15048
  have eq19859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19860 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19859
    | exact resolve eq19859 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19859
  have eq19871 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19860
       have r₂ := eq27
       grind)
    | exact resolve eq19860 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19860
  have eq19873 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19871
    | exact resolve eq19871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19871
  have eq19875 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19873
    | exact resolve eq19873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19873
  have eq19885 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19875 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19875
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19875
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19875
       grind)
    | exact resolve eq12 eq19875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19875
  have eq19923 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19885
       have r₂ := eq26
       grind)
    | exact resolve eq19885 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19885
  have eq19930 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19923
    | exact resolve eq19923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19923
  have eq19931 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq19930
  have eq20663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19931 eq99
    | exact resolve eq99 eq19931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19931
  have eq20671 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20663
  have eq20673 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20671
       have r₂ := eq27
       grind)
    | exact resolve eq20671 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20671
  have eq20683 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20673
       grind)
    | exact superpose eq20673 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq20673
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq20673
       grind)
    | exact resolve eq12 eq20673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20673
  have eq20721 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20683
       have r₂ := eq18
       grind)
    | exact resolve eq20683 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20683
  have eq20727 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20721
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20721
    | exact resolve eq20721 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20721
  have eq20728 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20727
  have eq20817 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq20728
       grind)
    | exact superpose eq20728 eq85
    | exact resolve eq85 eq20728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20728
  have eq20831 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20817
    | exact resolve eq20817 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20817
  have eq21185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20831 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq20831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21185
    | exact resolve eq21185 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21185
  have eq21199 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21188
       have r₂ := eq27
       grind)
    | exact resolve eq21188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21188
  have eq21201 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21199
    | exact resolve eq21199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21199
  have eq21203 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21201
    | exact resolve eq21201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21201
  have eq21204 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21203
  have eq21232 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21204 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21204
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21204
       grind)
    | exact resolve eq12 eq21204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21204
  have eq21272 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21232
       have r₂ := eq26
       grind)
    | exact resolve eq21232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21232
  have eq21280 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq21272
    | exact resolve eq21272 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21272
  have eq21281 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21280
  have eq21409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21281 eq20831
    | exact resolve eq20831 eq21281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20831 eq21281
  have eq21411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21409
  have eq21415 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21411
       have r₂ := eq27
       grind)
    | exact resolve eq21411 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21411
  have eq21417 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21415 eq27
    | exact resolve eq27 eq21415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21418 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21415 eq51
    | (have r₁ := eq51
       have r₂ := eq21415
       grind)
    | exact resolve eq51 eq21415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq21467 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21415 eq12643
    | exact resolve eq12643 eq21415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12643 eq21415
  have eq21477 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21418
  have eq21478 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8954 eq21467
    | exact resolve eq21467 eq8954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8954 eq21467
  have eq21512 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21477 eq95
    | exact resolve eq95 eq21477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq21513 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21477 eq99
    | exact resolve eq99 eq21477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq21477
  have eq21527 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq21513
  have eq21539 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq21512
    | exact resolve eq21512 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21512
  have eq21544 : y = (k y x) := by
    first
    | (have r₁ := eq21539
       have r₂ := eq50
       grind)
    | exact resolve eq21539 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq21539
  have eq21563 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq85
       have i₂ := eq21544
       grind)
    | exact superpose eq21544 eq85
    | exact resolve eq85 eq21544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21579 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq21563
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21563
    | exact resolve eq21563 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21563
  have eq26291 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq21527
       grind)
    | exact superpose eq21527 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21527
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21527
       grind)
    | exact resolve eq12 eq21527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21527
  have eq26335 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26291
       have r₂ := eq18
       grind)
    | exact resolve eq26291 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26291
  have eq26345 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26335
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26335
    | exact resolve eq26335 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26335
  have eq26346 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26345
  have eq26352 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26346
       have i₂ := eq21544
       grind)
    | exact superpose eq21544 eq26346
    | exact resolve eq26346 eq21544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26346
  have eq26361 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26352 eq29
    | exact resolve eq29 eq26352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq26352
  have eq26572 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq26361
    | exact resolve eq26361 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq26361
  have eq26573 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq26572
  have eq26584 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26573 eq20
    | exact resolve eq20 eq26573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26695 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq26756 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26584
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26584
    | exact resolve eq26584 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26584
  have eq26900 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26756 eq21478
    | exact resolve eq21478 eq26756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21478 eq26756
  have eq26918 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq26900
  have eq27190 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26918 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq26918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26918
  have eq27227 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq27190
  have eq27237 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27227
       have r₂ := eq21417
       grind)
    | exact resolve eq27227 eq21417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21417 eq27227
  have eq27404 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27237 eq150
    | exact resolve eq150 eq27237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq27237
  have eq27423 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq27404
    | exact resolve eq27404 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq27404
  have eq28195 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq4116 eq27423
    | exact resolve eq27423 eq4116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116
  have eq35006 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) y) ≠ X0 ∨ y = X0 ∨ (M.op (M.op (M.op x y) (M.op X0 X0)) y) = (k (M.op (M.op x y) (M.op X0 X0)) y) := by
    intro X0
    first
    | (have i₁ := eq884 y X0 x
       have i₂ := eq8476 X0 x
       grind)
    | exact superpose eq8476 eq884
    | (have j0 := eq884 y X0 x
       grind)
    | exact resolve eq884 eq8476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884 eq8476
  have eq164325 : (σ (k (k y x) (M.op x y))) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq5605 (k y x)
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq5605
    | exact resolve eq5605 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq5605
  have eq164445 : (M.op (σ (M.op x y)) (σ y)) = (σ (k (k y x) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq21579 eq164325
    | exact resolve eq164325 eq21579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164325
  have eq164466 : (M.op (σ (M.op x y)) (σ y)) = (k (k (σ y) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq193 eq164445
    | exact resolve eq164445 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq164445
  have eq164478 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq21579 eq164466
    | exact resolve eq164466 eq21579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164466
  have eq164485 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21579 eq164478
    | exact resolve eq164478 eq21579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21579 eq164478
  have eq165807 : (k y (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq164485 eq113
    | exact resolve eq113 eq164485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq164485
  have eq1311254 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq28195 eq4095
    | exact resolve eq4095 eq28195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095 eq28195
  have eq1317604 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1311254 eq27423
    | exact resolve eq27423 eq1311254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27423 eq1311254
  have eq1317669 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1317604
  have eq1317753 : x = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26573 eq1317669
    | exact resolve eq1317669 eq26573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26573
  have eq1317846 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1317669 eq7756
    | exact resolve eq7756 eq1317669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7756 eq1317669
  have eq1318181 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1317846
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1317846
    | exact resolve eq1317846 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317846
  have eq1318215 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1317753
       have r₂ := eq26695
       grind)
    | exact resolve eq1317753 eq26695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26695 eq1317753
  have eq1319858 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1318181
       have i₂ := eq1318215
       grind)
    | exact superpose eq1318215 eq1318181
    | exact resolve eq1318181 eq1318215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318181 eq1318215
  have eq1320260 : x = (M.op x y) := by grind
  clear eq1319858
  have eq1320515 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1320260 eq20
    | exact resolve eq20 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1320563 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1320260 eq204
    | exact resolve eq204 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1320568 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op y y))) := by
    intro X0
    first
    | exact superpose eq1320260 eq210
    | exact resolve eq210 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1320695 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq1320260 eq4054
    | exact resolve eq4054 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4054
  have eq1321035 : y = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq1320568 x
       have i₂ := eq11398 y x x
       grind)
    | exact superpose eq11398 eq1320568
    | exact resolve eq1320568 eq11398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11398 eq1320568
  have eq1321038 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1320563
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1320563
    | exact resolve eq1320563 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320563
  have eq1321083 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1320515
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1320515
    | exact resolve eq1320515 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320515
  have eq1321105 : y = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq1321035
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1321035
    | exact resolve eq1321035 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1321035
  have eq1321106 : x = (M.op y y) := by
    first
    | exact superpose eq1320260 eq1321038
    | exact resolve eq1321038 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321038
  have eq1321123 : y = (M.op y (M.op y x)) := by
    first
    | exact superpose eq1320260 eq1321105
    | exact resolve eq1321105 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321105
  have eq1324501 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1321083 eq26
    | exact resolve eq26 eq1321083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1326628 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1324501 eq165807
    | exact resolve eq165807 eq1324501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165807 eq1324501
  have eq1326986 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1326628
       have r₂ := eq27
       grind)
    | exact resolve eq1326628 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326628
  have eq1327036 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1320260 eq1326986
    | exact resolve eq1326986 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326986
  have eq1327060 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1327036
       have i₂ := eq21544
       grind)
    | exact superpose eq21544 eq1327036
    | exact resolve eq1327036 eq21544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21544 eq1327036
  have eq1327124 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1327060 eq15
    | exact resolve eq15 eq1327060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327060
  have eq1327684 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1327124
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1327124
    | exact resolve eq1327124 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327124
  have eq1327776 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1327684 eq27
    | exact resolve eq27 eq1327684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1335264 : y = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq1321123
       have i₂ := eq1320695
       grind)
    | exact superpose eq1320695 eq1321123
    | exact resolve eq1321123 eq1320695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321123
  have eq1335265 : y = (M.op x (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq1335264
       have i₂ := eq7840 x
       grind)
    | exact superpose eq7840 eq1335264
    | exact resolve eq1335264 eq7840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7840 eq1335264
  have eq1335266 : y = (M.op x (M.op x x)) := by
    first
    | exact superpose eq1320260 eq1335265
    | exact resolve eq1335265 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335265
  have eq1337199 : ∀ X0 : G, (M.op (M.op x (M.op X0 X0)) y) ≠ X0 ∨ y = X0 ∨ (M.op (M.op (M.op x y) (M.op X0 X0)) y) = (k (M.op (M.op x y) (M.op X0 X0)) y) := by
    intro X0
    first
    | exact superpose eq1320260 eq35006
    | (have j0 := eq35006 X0
       grind)
    | exact resolve eq35006 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35006
  have eq1337200 : ∀ X0 : G, (M.op (M.op x (M.op X0 X0)) y) ≠ X0 ∨ (M.op (M.op x (M.op X0 X0)) y) = (k (M.op x (M.op X0 X0)) y) ∨ y = X0 := by
    intro X0
    first
    | exact superpose eq1320260 eq1337199
    | (have j0 := eq1337199 X0
       grind)
    | exact resolve eq1337199 eq1320260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320260 eq1337199
  have eq1337326 : (M.op y y) ≠ (M.op y y) ∨ (M.op y y) = (k (M.op x (M.op (M.op y y) (M.op y y))) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1337200 (M.op y y)
       have i₂ := eq8122 y x (M.op y y)
       grind)
    | exact superpose eq8122 eq1337200
    | (have j0 := eq1337200 (M.op y y)
       grind)
    | (have r₁ := eq1337200 (M.op y y)
       have r₂ := eq8122 y x (M.op y y)
       grind)
    | exact resolve eq1337200 eq8122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8122 eq1337200
  have eq1337339 : (M.op y y) = (k (M.op x (M.op (M.op y y) (M.op y y))) y) ∨ y = (M.op y y) := by grind
  clear eq1337326
  have eq1337349 : (M.op y y) = (k (M.op x (M.op y (M.op y y))) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1337339
       have i₂ := eq15252 y y
       grind)
    | exact superpose eq15252 eq1337339
    | exact resolve eq1337339 eq15252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15252 eq1337339
  have eq1337435 : x = (k (M.op x (M.op y x)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1337349
       have i₂ := eq1321106
       grind)
    | exact superpose eq1321106 eq1337349
    | exact resolve eq1337349 eq1321106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337349
  have eq1337520 : x = (k (M.op x (M.op x x)) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1337435
       have i₂ := eq1320695
       grind)
    | exact superpose eq1320695 eq1337435
    | exact resolve eq1337435 eq1320695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320695 eq1337435
  have eq1337587 : x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1337520
       have i₂ := eq1335266
       grind)
    | exact superpose eq1335266 eq1337520
    | exact resolve eq1337520 eq1335266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1335266 eq1337520
  have eq1337646 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1337587
       have i₂ := eq1321106
       grind)
    | exact superpose eq1321106 eq1337587
    | exact resolve eq1337587 eq1321106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321106 eq1337587
  have eq1339617 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq86
       have i₂ := eq1337646
       grind)
    | exact superpose eq1337646 eq86
    | exact resolve eq86 eq1337646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1339675 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq5707 y y
       have i₂ := eq1337646
       grind)
    | exact superpose eq1337646 eq5707
    | (have j0 := eq5707 y y
       grind)
    | exact resolve eq5707 eq1337646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5707 eq1337646
  have eq1339683 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1339675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1339675
    | exact resolve eq1339675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339675
  have eq1339715 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1339617
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1339617
    | exact resolve eq1339617 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339617
  have eq1339719 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1339683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1339683
    | exact resolve eq1339683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339683
  have eq1339750 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1321083 eq1339715
    | exact resolve eq1339715 eq1321083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339715
  have eq1339754 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq1339719
    | exact resolve eq1339719 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1339719
  have eq1339773 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1327684 eq1339754
    | exact resolve eq1339754 eq1327684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327684 eq1339754
  have eq1339786 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1339773
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1339773
    | exact resolve eq1339773 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339773
  have eq1339787 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq1339786
  have eq1340090 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1339787 eq1481
    | exact resolve eq1481 eq1339787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq1339787
  have eq1341115 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1340090 eq1339750
    | exact resolve eq1339750 eq1340090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339750 eq1340090
  have eq1341146 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1341115
  have eq1341161 : x = y := by
    first
    | (have r₁ := eq1341146
       have r₂ := eq1327776
       grind)
    | exact resolve eq1341146 eq1327776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341146
  have eq1341188 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1341161
       grind)
    | exact superpose eq1341161 eq24
    | exact resolve eq24 eq1341161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1341161
  have eq1342367 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1341188
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1341188
    | exact resolve eq1341188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1341188
  have eq1342637 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1321083 eq1342367
    | exact resolve eq1342367 eq1321083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321083 eq1342367
  have eq1342762 : False := by grind
  exact eq1342762
