import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq25 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ (M.op X0 X0)) (M.op X1 X1)
       have i₂ := eq56 X0 (M.op X1 X1) (σ (M.op X0 X0))
       grind)
    | exact superpose eq56 eq62
    | exact resolve eq62 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq62
  have eq3418 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq95 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq95 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq95 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3435 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3418
  have eq3683 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3435
       grind)
    | exact superpose eq3435 eq16
    | exact resolve eq16 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3689 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq3435
       grind)
    | exact superpose eq3435 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3435
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3435
       grind)
    | exact resolve eq13 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435
  have eq3690 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3689
  have eq3691 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3690
  have eq3693 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3691
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3691
    | exact resolve eq3691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691
  have eq8641 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3693
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq3693
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq3693 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8644 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq3693
       grind)
    | exact superpose eq3693 eq10
    | exact resolve eq10 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq8663 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8641
  have eq8668 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8644
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8644
    | exact resolve eq8644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8669 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8663
       have r₂ := eq3683
       grind)
    | exact resolve eq8663 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683 eq8663
  have eq8670 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq8668
       have r₂ := eq13 x y
       grind)
    | exact resolve eq8668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8668
  have eq26469 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq8670
       grind)
    | exact superpose eq8670 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq8670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8670
  have eq26472 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26469
  have eq44008 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq26472
       grind)
    | exact superpose eq26472 eq16
    | exact resolve eq16 eq26472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26472
  have eq61537 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44008
       have i₂ := eq8669
       grind)
    | exact superpose eq8669 eq44008
    | exact resolve eq44008 eq8669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8669 eq44008
  have eq61538 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61537
  have eq61539 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq61538
  have eq80512 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq61539
       grind)
    | exact superpose eq61539 eq10
    | exact resolve eq10 eq61539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61539
  have eq80533 : x = y ∨ x = y := by
    first
    | (have i₁ := eq80512
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80512
    | exact resolve eq80512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80512
  have eq80534 : x = y := by grind
  clear eq80533
  have eq117302 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80534
       grind)
    | exact superpose eq80534 eq16
    | exact resolve eq16 eq80534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80534
  have eq117303 : False := by grind
  exact eq117303

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq9 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X2 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq25
    | exact resolve eq25 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 X0)
       have i₂ := eq25 X1 (M.op X0 X0) X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq95 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq28
    | (have j0 := eq28 X0 X1
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (σ (M.op X0 X0)) (M.op X1 X1)
       have i₂ := eq56 X0 (M.op X1 X1) (σ (M.op X0 X0))
       grind)
    | exact superpose eq56 eq62
    | exact resolve eq62 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq62
  have eq3418 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq95 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq95 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq95 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq3435 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3418
  have eq3683 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3435
       grind)
    | exact superpose eq3435 eq16
    | exact resolve eq16 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3689 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq3435
       grind)
    | exact superpose eq3435 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3435
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3435
       grind)
    | exact resolve eq13 eq3435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3435
  have eq3690 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3689
  have eq3691 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3690
  have eq3693 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3691
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq3691
    | exact resolve eq3691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691
  have eq8641 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3693
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq3693
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq3693 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8644 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq3693
       grind)
    | exact superpose eq3693 eq10
    | exact resolve eq10 eq3693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq8663 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8641
  have eq8668 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8644
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8644
    | exact resolve eq8644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8644
  have eq8669 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq8663
       have r₂ := eq3683
       grind)
    | exact resolve eq8663 eq3683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3683 eq8663
  have eq8670 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq8668
       have r₂ := eq13 y x
       grind)
    | exact resolve eq8668 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8668
  have eq26469 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq8670
       grind)
    | exact superpose eq8670 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq8670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq8670
  have eq26472 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq26469
  have eq44008 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq26472
       grind)
    | exact superpose eq26472 eq16
    | exact resolve eq16 eq26472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26472
  have eq61537 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq44008
       have i₂ := eq8669
       grind)
    | exact superpose eq8669 eq44008
    | exact resolve eq44008 eq8669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8669 eq44008
  have eq61538 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61537
  have eq61539 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq61538
  have eq80512 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq61539
       grind)
    | exact superpose eq61539 eq10
    | exact resolve eq10 eq61539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61539
  have eq80533 : x = y ∨ x = y := by
    first
    | (have i₁ := eq80512
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq80512
    | exact resolve eq80512 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80512
  have eq80534 : x = y := by grind
  clear eq80533
  have eq117302 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80534
       grind)
    | exact superpose eq80534 eq16
    | exact resolve eq16 eq80534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80534
  have eq117303 : False := by grind
  exact eq117303

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyx_pxx_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq418 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq76 X1
       grind)
    | exact superpose eq76 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq694 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq418 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq418
    | exact resolve eq418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq721 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq724 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq721 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq721 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq721 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq721 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq721
  have eq726 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq724 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq724
    | exact resolve eq724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq724 (σ X0) X1
       grind)
    | exact superpose eq724 eq15
    | (have j1 := eq724 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq771 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq726 X1 (τ X0)
       grind)
    | exact superpose eq726 eq19
    | (have j1 := eq726 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq726
  have eq905 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq771 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq771
    | exact resolve eq771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq949 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq905
    | (have j0 := eq905 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1087 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq735 x y
       grind)
    | exact superpose eq735 eq16
    | (have j1 := eq735 x y
       grind)
    | exact resolve eq16 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq1103 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1087
       have i₂ := eq949 x y
       grind)
    | exact superpose eq949 eq1087
    | (have j1 := eq949 (σ x) (σ y)
       grind)
    | (have r₁ := eq1087
       have r₂ := eq949 x y
       grind)
    | (have r₁ := eq1087
       have r₂ := eq949 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1087
       have r₂ := eq949 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1087 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949 eq1087
  have eq1104 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1103
  have eq1107 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq16
    | exact resolve eq16 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1108 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1107
       have r₂ := eq76 x
       grind)
    | exact resolve eq1107 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1109 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq16
    | exact resolve eq16 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1108
       grind)
    | exact superpose eq1108 eq10
    | exact resolve eq10 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq1156 : x = y := by
    first
    | (have i₁ := eq1110
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1110
    | exact resolve eq1110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1157 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1109
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq1109
    | exact resolve eq1109 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1109
  have eq1158 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1157
       have i₂ := eq1156
       grind)
    | exact superpose eq1156 eq1157
    | exact resolve eq1157 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156 eq1157
  have eq1159 : False := by grind
  exact eq1159

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_y_pxy_y_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq57 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq70 : y ≠ (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
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
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq44
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq44 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq122 eq79
    | (have j0 := eq79 (σ x) (σ y)
       grind)
    | exact resolve eq79 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq189
    | exact resolve eq189 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq193 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq190
       have r₂ := eq27
       grind)
    | exact resolve eq190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq195 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq193
    | exact resolve eq193 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq197 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq195 eq27
    | exact resolve eq27 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq79 (σ X0) sF3
       grind)
    | exact superpose eq79 eq40
    | (have j1 := eq79 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq79
  have eq471 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq195 eq71
    | (have r₁ := eq71
       have r₂ := eq195
       grind)
    | exact resolve eq71 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq195
  have eq472 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq471
  have eq474 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq472 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq472
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq472
       grind)
    | exact resolve eq13 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472
  have eq557 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq474 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474
  have eq560 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq557
    | exact resolve eq557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq122 eq560
    | exact resolve eq560 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq560
  have eq572 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq564
  have eq575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq572
       have r₂ := eq197
       grind)
    | exact resolve eq572 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq572
  have eq576 : y = (M.op x y) := by
    first
    | (have r₁ := eq575
       have r₂ := eq27
       grind)
    | exact resolve eq575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq577 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq576 eq20
    | exact resolve eq20 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq579 : y ≠ y ∨ (M.op x x) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq576 eq70
    | (have r₁ := eq70
       have r₂ := eq576
       grind)
    | exact resolve eq70 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq586 : (M.op x x) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq579
  have eq594 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq577
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq577
    | exact resolve eq577 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq597 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq594 eq26
    | exact resolve eq26 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1206 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq586
       grind)
    | exact superpose eq586 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq586
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq586
       grind)
    | exact resolve eq13 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq2819 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq594 eq212
    | (have j0 := eq212 X0
       grind)
    | exact resolve eq212 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2820 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq594 eq2819
    | (have j0 := eq2819 X0
       grind)
    | exact resolve eq2819 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819
  have eq3011 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2820 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2820
    | (have j0 := eq2820 x
       grind)
    | exact resolve eq2820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2820
  have eq3019 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq597 eq3011
    | exact resolve eq3011 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011
  have eq3040 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3019
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3019
    | exact resolve eq3019 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3019
  have eq3056 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq594 eq3040
    | exact resolve eq3040 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq597 eq3056
    | exact resolve eq3056 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq3056
  have eq3073 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3067
       have r₂ := eq27
       grind)
    | exact resolve eq3067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3067
  have eq3082 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3073 eq57
    | exact resolve eq57 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq3073
  have eq3088 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq576 eq3082
    | exact resolve eq3082 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq417704 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1206 X0
       have i₂ := eq3088
       grind)
    | exact superpose eq3088 eq1206
    | (have j0 := eq1206 X0
       grind)
    | exact resolve eq1206 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq417721 : y = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq417704 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417704
  have eq417724 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq417721
       have i₂ := eq3088
       grind)
    | exact superpose eq3088 eq417721
    | exact resolve eq417721 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088 eq417721
  have eq417734 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq417724
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq417724
    | exact resolve eq417724 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq417724
  have eq417738 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq576 eq417734
    | exact resolve eq417734 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq417734
  have eq417739 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq417738
  have eq417781 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq417739 eq15
    | exact resolve eq15 eq417739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417739
  have eq418200 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq417781
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq417781
    | exact resolve eq417781 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq417781
  have eq418234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq594 eq418200
    | exact resolve eq418200 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq418200
  have eq418250 : False := by grind
  exact eq418250

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | (have i₁ := eq76 X0
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 (M.op X0 X0) (σ (M.op X1 X1))
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq401 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq401 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq401 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq401 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq401
  have eq417 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq406
    | exact resolve eq406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq406 (σ X1) X0
       grind)
    | exact superpose eq406 eq15
    | (have j1 := eq406 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq457 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq417 (τ X0) X1
       grind)
    | exact superpose eq417 eq19
    | (have j1 := eq417 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq417
  have eq584 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq457 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq457
    | exact resolve eq457 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq622 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq584 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq584
    | (have j0 := eq584 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq584 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq799 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq428 x y
       grind)
    | exact superpose eq428 eq16
    | (have j1 := eq428 x y
       grind)
    | exact resolve eq16 eq428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq811 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq799
       have i₂ := eq622 x y
       grind)
    | exact superpose eq622 eq799
    | (have j1 := eq622 (σ x) (σ y)
       grind)
    | (have r₁ := eq799
       have r₂ := eq622 x y
       grind)
    | (have r₁ := eq799
       have r₂ := eq622 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq799
       have r₂ := eq622 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq799 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq799
  have eq812 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq811
  have eq815 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq812
       grind)
    | exact superpose eq812 eq16
    | exact resolve eq16 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq816 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq815
       have r₂ := eq76 x
       grind)
    | exact resolve eq815 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815
  have eq817 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq16
    | exact resolve eq16 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq818 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq10
    | exact resolve eq10 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq860 : x = y := by
    first
    | (have i₁ := eq818
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq818
    | exact resolve eq818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq861 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq817
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq817
    | exact resolve eq817 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq817
  have eq862 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq861
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq861
    | exact resolve eq861 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq861
  have eq863 : False := by grind
  exact eq863

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_x_pyx_x_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq81 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
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
  clear eq17
  have eq805 : ∀ X0 X1 X2 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op X2 (τ X0)) ∨ (k X0 (σ X2)) = (σ (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq81 X2 X0
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq81 X2 X0
       grind)
    | (have r₁ := eq12 (τ X1) X1
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) X1
       have r₂ := eq81 (τ X1) X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq809 : ∀ X0 X1 X2 : G, (k X0 (σ X2)) = (σ (M.op X2 (τ X0))) ∨ (τ X0) = (M.op X2 (τ X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq805 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq9720 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq809 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq809
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq9825 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9720 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9720
    | (have j0 := eq9720 X0 X1 X2
       grind)
    | exact resolve eq9720 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9720
  have eq23081 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X0 X1) = X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq9825 X1 X0 X2
       grind)
    | exact superpose eq9825 eq10
    | (have j1 := eq9825 X1 X0 X2
       grind)
    | exact resolve eq10 eq9825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9825
  have eq23173 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X1 X2) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23081 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq23081
    | (have j0 := eq23081 X0 X1 X0
       grind)
    | exact resolve eq23081 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23081
  have eq23455 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq23173 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23173
  have eq23456 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq23455 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23455
  have eq23897 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq23456 X1 (σ X0)
       grind)
    | exact superpose eq23456 eq22
    | (have j1 := eq23456 X1 (σ X0)
       grind)
    | exact resolve eq22 eq23456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq23959 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq23456 (σ X1) (σ X0)
       grind)
    | exact superpose eq23456 eq15
    | (have j1 := eq23456 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq23456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23456
  have eq25842 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq23897 X1 X0
       grind)
    | exact superpose eq23897 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq23897 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq23897 X0 X1
       grind)
    | exact resolve eq13 eq23897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23897
  have eq25843 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq25842 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25842
  have eq31213 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23959 x y
       grind)
    | exact superpose eq23959 eq16
    | (have j1 := eq23959 x y
       grind)
    | exact resolve eq16 eq23959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31346 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq23959 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23959
  have eq31642 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31346 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq31346
    | (have j0 := eq31346 (τ X1) (τ X0)
       grind)
    | exact resolve eq31346 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31759 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31642 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq31642
    | (have j0 := eq31642 X0 X1
       grind)
    | exact resolve eq31642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31642
  have eq31810 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31759 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31759
    | (have j0 := eq31759 X0 X1
       grind)
    | exact resolve eq31759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31759
  have eq31832 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31810 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31810
    | (have j0 := eq31810 X0 X1
       grind)
    | exact resolve eq31810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31810
  have eq31849 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31832 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq31832
    | (have j0 := eq31832 X0 X1
       grind)
    | exact resolve eq31832 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31832
  have eq80734 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25843 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25843
    | (have j0 := eq25843 X1 X1
       grind)
    | exact resolve eq25843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25843
  have eq81148 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq80734 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq80734
    | (have j0 := eq80734 X0 X1
       grind)
    | exact resolve eq80734 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq80734
  have eq81455 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq81148 X0 X1
       grind)
    | exact superpose eq81148 eq11
    | (have j1 := eq81148 X0 X1
       grind)
    | exact resolve eq11 eq81148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81148
  have eq81675 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq81455 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq81455
    | (have j0 := eq81455 X0 X1
       grind)
    | exact resolve eq81455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81455
  have eq81740 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq81675 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq81675 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq81675 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81675
  have eq83017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq31213
       have i₂ := eq81740 x y
       grind)
    | exact superpose eq81740 eq31213
    | (have j1 := eq81740 x y
       grind)
    | exact resolve eq31213 eq81740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31213
  have eq83019 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq81740 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81740
  have eq83021 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq83017
  have eq84458 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq83019 (σ y) (σ x)
       have i₂ := eq83021
       grind)
    | exact superpose eq83021 eq83019
    | (have j0 := eq83019 (σ y) (σ x)
       grind)
    | (have r₁ := eq83019 (σ y) (σ x)
       have r₂ := eq83021
       grind)
    | exact resolve eq83019 eq83021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83021
  have eq84459 : (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq84458
  have eq84461 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq84459
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq84459
    | exact resolve eq84459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84459
  have eq85517 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq31346 x y
       have i₂ := eq84461
       grind)
    | exact superpose eq84461 eq31346
    | (have j0 := eq31346 x y
       grind)
    | (have r₁ := eq31346 x y
       have r₂ := eq84461
       grind)
    | exact resolve eq31346 eq84461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84461
  have eq85547 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq85517
  have eq85558 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq31346 x y
       grind)
    | (have r₁ := eq85547
       have r₂ := eq31346 x y
       grind)
    | exact resolve eq85547 eq31346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31346 eq85547
  have eq85566 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85558
       grind)
    | exact superpose eq85558 eq16
    | exact resolve eq16 eq85558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85570 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq83019 (σ y) (σ x)
       have i₂ := eq85558
       grind)
    | exact superpose eq85558 eq83019
    | (have j0 := eq83019 (σ y) (σ x)
       grind)
    | (have r₁ := eq83019 (σ y) (σ x)
       have r₂ := eq85558
       grind)
    | exact resolve eq83019 eq85558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83019 eq85558
  have eq85571 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq85570
  have eq85573 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq85571
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq85571
    | exact resolve eq85571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85571
  have eq86755 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq85573
       grind)
    | exact superpose eq85573 eq10
    | exact resolve eq10 eq85573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85573
  have eq87010 : y = (k y x) := by
    first
    | (have i₁ := eq86755
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq86755
    | exact resolve eq86755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86755
  have eq87251 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31849 y x
       have i₂ := eq87010
       grind)
    | exact superpose eq87010 eq31849
    | (have j0 := eq31849 y x
       grind)
    | (have r₁ := eq31849 y x
       have r₂ := eq87010
       grind)
    | exact resolve eq31849 eq87010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31849 eq87010
  have eq87277 : y = (M.op x y) := by grind
  clear eq87251
  have eq87293 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq85566
       have i₂ := eq87277
       grind)
    | exact superpose eq87277 eq85566
    | exact resolve eq85566 eq87277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85566 eq87277
  have eq87301 : False := by grind
  exact eq87301

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_pxy_pxx_pxy_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq98
    | exact resolve eq98 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq100
  have eq177 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq182 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq186 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq764 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq186 x y
       grind)
    | exact superpose eq186 eq16
    | (have j1 := eq186 x y
       grind)
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq995 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1051 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq995 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq995
    | (have j0 := eq995 X0 X1
       grind)
    | exact resolve eq995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq5066 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq764
       have i₂ := eq1051 y x
       grind)
    | exact superpose eq1051 eq764
    | (have j1 := eq1051 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq764
       have r₂ := eq1051 y x
       grind)
    | (have r₁ := eq764
       have r₂ := eq1051 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq764
       have r₂ := eq1051 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq764 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq1051
  have eq5067 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5066
  have eq5069 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5067
       grind)
    | exact superpose eq5067 eq16
    | exact resolve eq16 eq5067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5067
  have eq5070 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5069
       have r₂ := eq82 x
       grind)
    | exact resolve eq5069 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5069
  have eq5077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5070
       grind)
    | exact superpose eq5070 eq103
    | exact resolve eq103 eq5070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5070
  have eq5093 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5077
       have r₂ := eq16
       grind)
    | exact resolve eq5077 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5077
  have eq5096 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5093
       grind)
    | exact superpose eq5093 eq10
    | exact resolve eq10 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5149 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5096
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5096
    | exact resolve eq5096 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096
  have eq5152 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5149
       grind)
    | exact superpose eq5149 eq16
    | exact resolve eq16 eq5149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5153 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5152
       have r₂ := eq82 x
       grind)
    | exact resolve eq5152 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq5152
  have eq5162 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5153
       grind)
    | exact superpose eq5153 eq10
    | exact resolve eq10 eq5153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153
  have eq5215 : y = (M.op x x) := by
    first
    | (have i₁ := eq5162
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5162
    | exact resolve eq5162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq5226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq5215
       grind)
    | exact superpose eq5215 eq103
    | exact resolve eq103 eq5215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq5215
  have eq5241 : False := by grind
  exact eq5241

/-- `Equation3058`: `x = (((x ◇ x) ◇ y) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation3058 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3058 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3058.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq18
    | exact resolve eq18 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq61
    | exact resolve eq61 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq61
  have eq75 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq154 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq181 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq154
    | (have j0 := eq154 X0 X1
       grind)
    | exact resolve eq154 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq154
  have eq185 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq181 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq181 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq188 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq335 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188
    | exact resolve eq188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq188 (σ X0) X1
       grind)
    | exact superpose eq188 eq15
    | (have j1 := eq188 (σ X0) X1
       grind)
    | exact resolve eq15 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq356 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq342 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq342
    | (have j0 := eq342 X0 X1
       grind)
    | exact resolve eq342 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq342
  have eq377 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq335 (τ X1) X0
       grind)
    | exact superpose eq335 eq17
    | (have j1 := eq335 (τ X1) X0
       grind)
    | exact resolve eq17 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq335
  have eq888 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq377
    | exact resolve eq377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq941 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq3711 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq356 x y
       grind)
    | exact superpose eq356 eq16
    | (have j1 := eq356 x y
       grind)
    | exact resolve eq16 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3732 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq3768 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3711
       have i₂ := eq941 y x
       grind)
    | exact superpose eq941 eq3711
    | (have j1 := eq941 y x
       grind)
    | (have r₁ := eq3711
       have r₂ := eq941 y x
       grind)
    | exact resolve eq3711 eq941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941 eq3711
  have eq3769 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3768
  have eq3896 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3769
       grind)
    | exact superpose eq3769 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3769
       grind)
    | exact resolve eq13 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3898 : y = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3896
  have eq3909 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3732 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3732
    | (have j0 := eq3732 (τ X1) (τ X0)
       grind)
    | exact resolve eq3732 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq3957 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3909 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq3909
    | (have j0 := eq3909 X0 X1
       grind)
    | exact resolve eq3909 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3909
  have eq3978 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3957 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3957
    | (have j0 := eq3957 X0 X1
       grind)
    | exact resolve eq3957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957
  have eq3992 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3978 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3978
    | (have j0 := eq3978 X0 X1
       grind)
    | exact resolve eq3978 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978
  have eq4003 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3992 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3992
    | (have j0 := eq3992 X0 X1
       grind)
    | exact resolve eq3992 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4008 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4003 X0 X1
       have i₂ := eq67 X1
       grind)
    | exact superpose eq67 eq4003
    | (have j0 := eq4003 X0 X1
       grind)
    | exact resolve eq4003 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq4003
  have eq13772 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3898
       grind)
    | exact superpose eq3898 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3898
       grind)
    | exact resolve eq12 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898
  have eq13773 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq13772
  have eq60643 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13773
       grind)
    | exact superpose eq13773 eq16
    | exact resolve eq16 eq13773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq60899 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq60643
       have i₂ := eq3769
       grind)
    | exact superpose eq3769 eq60643
    | exact resolve eq60643 eq3769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769 eq60643
  have eq60901 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq60899
  have eq60902 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq60901
  have eq60911 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq75 x (σ y)
       have i₂ := eq60902
       grind)
    | exact superpose eq60902 eq75
    | (have j0 := eq75 x (σ y)
       grind)
    | (have r₁ := eq75 x (σ y)
       have r₂ := eq60902
       grind)
    | exact resolve eq75 eq60902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq60938 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq60911
  have eq60941 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq60938
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq60938
    | exact resolve eq60938 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60938
  have eq89126 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq60941
       grind)
    | exact superpose eq60941 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq60941
       grind)
    | exact resolve eq12 eq60941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60941
  have eq89137 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq89126
  have eq89149 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq89137
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq89137
    | exact resolve eq89137 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89137
  have eq903305 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq60902
       have i₂ := eq89149
       grind)
    | exact superpose eq89149 eq60902
    | exact resolve eq60902 eq89149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60902 eq89149
  have eq903521 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq903305
  have eq903725 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3732 x y
       have i₂ := eq903521
       grind)
    | exact superpose eq903521 eq3732
    | (have j0 := eq3732 x y
       grind)
    | (have r₁ := eq3732 x y
       have r₂ := eq903521
       grind)
    | exact resolve eq3732 eq903521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903728 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4008 y x
       have i₂ := eq903521
       grind)
    | exact superpose eq903521 eq4008
    | (have j0 := eq4008 y x
       grind)
    | (have r₁ := eq4008 y x
       have r₂ := eq903521
       grind)
    | exact resolve eq4008 eq903521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903521
  have eq903955 : (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq903728
  have eq903957 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq903725
  have eq903966 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3732 x y
       grind)
    | (have r₁ := eq903957
       have r₂ := eq3732 x y
       grind)
    | exact resolve eq903957 eq3732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732 eq903957
  have eq907622 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq903966
       grind)
    | exact superpose eq903966 eq16
    | exact resolve eq16 eq903966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903966
  have eq910907 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq907622
       have i₂ := eq903955
       grind)
    | exact superpose eq903955 eq907622
    | exact resolve eq907622 eq903955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903955
  have eq910917 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq910907
  have eq910973 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq910917
       grind)
    | exact superpose eq910917 eq10
    | exact resolve eq10 eq910917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910917
  have eq911477 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq910973
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq910973
    | exact resolve eq910973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910973
  have eq914545 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4008 y x
       have i₂ := eq911477
       grind)
    | exact superpose eq911477 eq4008
    | (have j0 := eq4008 y x
       grind)
    | (have r₁ := eq4008 y x
       have r₂ := eq911477
       grind)
    | exact resolve eq4008 eq911477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4008 eq911477
  have eq914772 : (M.op x y) = (M.op x x) := by grind
  clear eq914545
  have eq914811 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq907622
       have i₂ := eq914772
       grind)
    | exact superpose eq914772 eq907622
    | exact resolve eq907622 eq914772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907622 eq914772
  have eq914816 : False := by grind
  exact eq914816
