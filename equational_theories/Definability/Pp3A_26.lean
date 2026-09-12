import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation653`: `x = x ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation653 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law653 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law653.models_iff G M).mp hM
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
  have eq286 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq289 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq287 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq287 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq287 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq289 (σ X0)
       grind)
    | exact superpose eq289 eq15
    | exact resolve eq15 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq300 X0
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq300
    | exact resolve eq300 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq300
  have eq366 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq319 X0
       grind)
    | exact superpose eq319 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq319 X0
       grind)
    | exact superpose eq319 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       have j1 := eq367 X0 X1
       grind)
    | (have r₁ := eq366 X0 X1
       have r₂ := eq367 X0 X1
       grind)
    | exact resolve eq366 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq525 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq368
    | exact resolve eq368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq368 X1 (σ X0)
       grind)
    | exact superpose eq368 eq15
    | (have j1 := eq368 X1 (σ X0)
       grind)
    | exact resolve eq15 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq576 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq525 X1 (τ X0)
       grind)
    | exact superpose eq525 eq17
    | (have j1 := eq525 X1 (τ X0)
       grind)
    | exact resolve eq17 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq525
  have eq764 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq576 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq576
    | exact resolve eq576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq824 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq764 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq764
    | (have j0 := eq764 X0 X1
       grind)
    | exact resolve eq764 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1469 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq536 x y
       grind)
    | exact superpose eq536 eq16
    | (have j1 := eq536 x y
       grind)
    | exact resolve eq16 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1503 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq1646 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1469
       have i₂ := eq824 x y
       grind)
    | exact superpose eq824 eq1469
    | (have j1 := eq824 (σ x) (σ y)
       grind)
    | (have r₁ := eq1469
       have r₂ := eq824 x y
       grind)
    | exact resolve eq1469 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1647 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1646
  have eq1650 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1647
       grind)
    | exact superpose eq1647 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1647
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1647
       grind)
    | exact resolve eq13 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1661 : y = (k x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1650
  have eq2637 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1503 x y
       have i₂ := eq1661
       grind)
    | exact superpose eq1661 eq1503
    | (have j0 := eq1503 x y
       grind)
    | exact resolve eq1503 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq1661
  have eq2644 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2637
  have eq2645 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2644
  have eq2651 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq16
    | exact resolve eq16 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2653 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2645
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq2645
       grind)
    | exact resolve eq13 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq2664 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2653
  have eq2667 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2664
       have i₂ := eq319 y
       grind)
    | exact superpose eq319 eq2664
    | exact resolve eq2664 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319 eq2664
  have eq2669 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2667
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2667
    | exact resolve eq2667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667
  have eq4353 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq824 x y
       have i₂ := eq2669
       grind)
    | exact superpose eq2669 eq824
    | (have j0 := eq824 x y
       grind)
    | exact resolve eq824 eq2669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2669
  have eq4410 : y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq4353
       have r₂ := eq2651
       grind)
    | exact resolve eq4353 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4353
  have eq4444 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2651
       have i₂ := eq4410
       grind)
    | exact superpose eq4410 eq2651
    | exact resolve eq2651 eq4410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4410
  have eq4469 : (σ y) ≠ (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq4444
  have eq4470 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq4469
  have eq4549 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq367 y X0
       have i₂ := eq4470
       grind)
    | exact superpose eq4470 eq367
    | (have j0 := eq367 y X0
       grind)
    | (have r₁ := eq367 y x
       have r₂ := eq4470
       grind)
    | exact resolve eq367 eq4470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq4584 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq4549 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4549
  have eq4586 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq4584 X0
       have j1 := eq367 y X0
       grind)
    | (have r₁ := eq4584 X0
       have r₂ := eq367 y x
       grind)
    | exact resolve eq4584 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq4584
  have eq4604 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq4586 (σ X0)
       grind)
    | exact superpose eq4586 eq15
    | exact resolve eq15 eq4586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4586
  have eq4749 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4604 x
       grind)
    | exact superpose eq4604 eq16
    | exact resolve eq16 eq4604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604
  have eq4854 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4749
       have i₂ := eq824 x y
       grind)
    | exact superpose eq824 eq4749
    | (have j1 := eq824 x y
       grind)
    | (have r₁ := eq4749
       have r₂ := eq824 x y
       grind)
    | exact resolve eq4749 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq4855 : y = (M.op x y) := by grind
  clear eq4854
  have eq4860 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2651
       have i₂ := eq4855
       grind)
    | exact superpose eq4855 eq2651
    | exact resolve eq2651 eq4855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq4855
  have eq4884 : y = (M.op y y) := by grind
  clear eq4860
  have eq4887 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq4884
       grind)
    | exact superpose eq4884 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq4884
       grind)
    | exact resolve eq12 eq4884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4884
  have eq4927 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq4887 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4887
  have eq4952 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq4749
       have i₂ := eq4927 x
       grind)
    | exact superpose eq4927 eq4749
    | exact resolve eq4749 eq4927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4749 eq4927
  have eq4958 : False := by grind
  exact eq4958

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq81 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81
    | exact resolve eq81 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq88
    | exact resolve eq88 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq104 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq104
    | (have j0 := eq104 (σ X0)
       grind)
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq44
    | (have j1 := eq104 x
       grind)
    | exact resolve eq44 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq574 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq51 X1 X4 x x
       have i₂ := eq51 X1 X0 x x
       grind)
    | (have i₁ := eq51 X0 X1 x x
       have i₂ := eq51 X0 (M.op x x) x x
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq51 X1 X0 x X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq51 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq51 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq655 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq574 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq574
    | (have j0 := eq574 x y X0
       grind)
    | exact resolve eq574 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq574
    | (have j0 := eq574 X0 (σ y) (σ x)
       grind)
    | exact resolve eq574 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq712 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 X0) X0
       have i₂ := eq655 (M.op X0 X0)
       grind)
    | exact superpose eq655 eq14
    | exact resolve eq14 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq734 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq656 eq14
    | exact resolve eq14 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq3607 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X4 (M.op X4 (M.op X2 (M.op X2 X0)))))) = X0 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq591 X4 (M.op X2 (M.op X2 X0)) X3 x
       have i₂ := eq592 X2 X0 x
       grind)
    | exact superpose eq592 eq591
    | exact resolve eq591 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3642 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq591
    | (have j0 := eq591 (σ x) (σ y) X1 X0
       grind)
    | exact resolve eq591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq5056 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq463 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq14879 : ∀ X0 X1 : G, (σ y) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))))) := by
    intro X0 X1
    first
    | exact superpose eq3642 eq14
    | exact resolve eq14 eq3642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3642
  have eq32077 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq89 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq32077
    | exact resolve eq32077 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32077
  have eq32089 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq32078
       have r₂ := eq28
       grind)
    | exact resolve eq32078 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32078
  have eq32091 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq32089
    | exact resolve eq32089 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32089
  have eq32181 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq32091 eq592
    | exact resolve eq592 eq32091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32091
  have eq32185 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq734 eq32181
    | exact resolve eq32181 eq734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq32181
  have eq32192 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq32185
  have eq32295 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq32192
    | exact resolve eq32192 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32192
  have eq32567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32295 eq89
    | exact resolve eq89 eq32295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq32295
  have eq32575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq32567
  have eq32577 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq32575
       have r₂ := eq28
       grind)
    | exact resolve eq32575 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32575
  have eq32667 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op x (M.op x y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq592 x x X0
       have i₂ := eq32577
       grind)
    | exact superpose eq32577 eq592
    | exact resolve eq592 eq32577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq32577
  have eq32671 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq712 eq32667
    | exact resolve eq32667 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712 eq32667
  have eq32927 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq32671
  have eq33030 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32927
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32927
    | exact resolve eq32927 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32927
  have eq33057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq68
       have i₂ := eq33030
       grind)
    | exact superpose eq33030 eq68
    | exact resolve eq68 eq33030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq33030
  have eq33075 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq33057
    | exact resolve eq33057 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33057
  have eq33109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33075 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq33075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq33109
    | exact resolve eq33109 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33109
  have eq33123 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq33112
       have r₂ := eq28
       grind)
    | exact resolve eq33112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33112
  have eq33125 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq33123
    | exact resolve eq33123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33123
  have eq47178 : ∀ X0 X1 : G, (σ x) = (M.op X0 (M.op X0 (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq33125 eq3607
    | exact resolve eq3607 eq33125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607 eq33125
  have eq47195 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14879 eq47178
    | exact resolve eq47178 eq14879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14879 eq47178
  have eq47196 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47195
  have eq47211 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47196
  have eq47357 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq47211
    | exact resolve eq47211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47211
  have eq47423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq47357 eq33075
    | exact resolve eq33075 eq47357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33075 eq47357
  have eq47425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq47423
  have eq47433 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq47425
       have r₂ := eq28
       grind)
    | exact resolve eq47425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47425
  have eq47436 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq47433 eq30
    | exact resolve eq30 eq47433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq47433
  have eq47575 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq47436
    | exact resolve eq47436 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq47436
  have eq47576 : x = y := by grind
  clear eq47575
  have eq47577 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq47576
       grind)
    | exact superpose eq47576 eq19
    | exact resolve eq19 eq47576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq47578 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq47576
       grind)
    | exact superpose eq47576 eq25
    | exact resolve eq25 eq47576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47576
  have eq47717 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq47578
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq47578
    | exact resolve eq47578 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47578
  have eq47718 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq47717 eq27
    | exact resolve eq27 eq47717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq47717
  have eq47868 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq468
       have i₂ := eq47577
       grind)
    | exact superpose eq47577 eq468
    | exact resolve eq468 eq47577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq47875 : (k (M.op x y) x) = (M.op x (M.op x y)) := by grind
  have eq48013 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq47868
    | exact resolve eq47868 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47868
  have eq48031 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq50275 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48013 eq104
    | (have j0 := eq104 (σ x)
       grind)
    | exact resolve eq104 eq48013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq50276 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47718 eq50275
    | exact resolve eq50275 eq47718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50275
  have eq50288 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq50276
       have r₂ := eq28
       grind)
    | exact resolve eq50276 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50276
  have eq50294 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47718 eq50288
    | exact resolve eq50288 eq47718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50288
  have eq50333 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50294 eq48031
    | exact resolve eq48031 eq50294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48031 eq50294
  have eq50340 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq47718 eq50333
    | exact resolve eq50333 eq47718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50333
  have eq52137 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50340 eq48013
    | exact resolve eq48013 eq50340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48013 eq50340
  have eq52142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq52137
  have eq52146 : x = (M.op x y) := by
    first
    | (have r₁ := eq52142
       have r₂ := eq28
       grind)
    | exact resolve eq52142 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52142
  have eq52154 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq52146 eq21
    | exact resolve eq21 eq52146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq52277 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq52146 eq47875
    | exact resolve eq47875 eq52146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47875
  have eq52289 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq52277
       have i₂ := eq47577
       grind)
    | exact superpose eq47577 eq52277
    | exact resolve eq52277 eq47577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47577 eq52277
  have eq52375 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq52154
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52154
    | exact resolve eq52154 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52154
  have eq52380 : x = (k x x) := by
    first
    | exact superpose eq52146 eq52289
    | exact resolve eq52289 eq52146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52146 eq52289
  have eq52892 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5056 x
       have i₂ := eq52380
       grind)
    | exact superpose eq52380 eq5056
    | (have j0 := eq5056 x
       grind)
    | exact resolve eq5056 eq52380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5056 eq52380
  have eq52896 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq52892
  have eq52906 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq52896
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52896
    | exact resolve eq52896 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52896
  have eq52918 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47718 eq52906
    | exact resolve eq52906 eq47718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47718 eq52906
  have eq52929 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq52375 eq52918
    | exact resolve eq52918 eq52375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52375 eq52918
  have eq52938 : False := by grind
  exact eq52938

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq70 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq74
    | (have j0 := eq74 X0 X1
       grind)
    | exact resolve eq74 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq240 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq79 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq250 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq254 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       have j1 := eq70 X1 (σ X0)
       grind)
    | (have r₁ := eq250 X0 X0
       have r₂ := eq70 X0 (σ X0)
       grind)
    | exact resolve eq250 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq255 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq240 X0 X1
       have j1 := eq70 X1 (σ X0)
       grind)
    | (have r₁ := eq240 X0 X0
       have r₂ := eq70 X0 (σ X0)
       grind)
    | exact resolve eq240 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq240
  have eq266 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq254
    | (have j0 := eq254 X0 X1
       grind)
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq267 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq268 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq255
    | (have j0 := eq255 X0 X1
       grind)
    | exact resolve eq255 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq276 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq267
    | (have j0 := eq267 X0 X1
       grind)
    | exact resolve eq267 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq267
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq268
    | (have j0 := eq268 X0 X1
       grind)
    | exact resolve eq268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq278 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq284 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       have j1 := eq276 X0 X1
       grind)
    | (have r₁ := eq278 X0 X1
       have r₂ := eq276 X0 X1
       grind)
    | exact resolve eq278 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq278
  have eq286 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq284 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq284
    | exact resolve eq284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq284 x y
       grind)
    | exact superpose eq284 eq16
    | exact resolve eq16 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq383 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq286 X0 (τ X1)
       grind)
    | exact superpose eq286 eq18
    | exact resolve eq18 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq286
  have eq400 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq383 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq383
    | exact resolve eq383 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq408 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq400
    | exact resolve eq400 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq420 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq297
       have i₂ := eq408 x y
       grind)
    | exact superpose eq408 eq297
    | exact resolve eq297 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq408
  have eq421 : False := by grind
  exact eq421

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq75 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq533 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq9381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9382 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9381
    | exact resolve eq9381 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9381
  have eq9393 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq9382
       have r₂ := eq28
       grind)
    | exact resolve eq9382 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9382
  have eq9395 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9393
    | exact resolve eq9393 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9393
  have eq9407 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq9395
  have eq9434 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq9407
    | exact resolve eq9407 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9407
  have eq9496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9434 eq116
    | exact resolve eq116 eq9434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9434
  have eq9504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9496
  have eq9506 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9504
       have r₂ := eq28
       grind)
    | exact resolve eq9504 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9504
  have eq9519 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9506
  have eq9546 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9519
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9519
    | exact resolve eq9519 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9519
  have eq9749 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq9546
       grind)
    | exact superpose eq9546 eq45
    | exact resolve eq45 eq9546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546
  have eq9763 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq9749
    | exact resolve eq9749 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9749
  have eq9935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9763 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9935
    | exact resolve eq9935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9935
  have eq9949 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9938
       have r₂ := eq28
       grind)
    | exact resolve eq9938 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9938
  have eq9951 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq9949
    | exact resolve eq9949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9949
  have eq9952 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9951
  have eq9965 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9952
  have eq9992 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq9965
    | exact resolve eq9965 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9965
  have eq10709 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9992 eq9763
    | exact resolve eq9763 eq9992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9763 eq9992
  have eq10712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10709
  have eq10716 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10712
       have r₂ := eq28
       grind)
    | exact resolve eq10712 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10712
  have eq10718 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10716 eq28
    | exact resolve eq28 eq10716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10721 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10716 eq76
    | (have r₁ := eq76
       have r₂ := eq10716
       grind)
    | exact resolve eq76 eq10716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq10716
  have eq10745 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10721
  have eq11552 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10745 eq116
    | exact resolve eq116 eq10745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11569 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq11552
  have eq11583 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11569
       have r₂ := eq10718
       grind)
    | exact resolve eq11569 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11569
  have eq11600 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq11583
  have eq11636 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11600
    | exact resolve eq11600 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11600
  have eq12022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11636 eq116
    | exact resolve eq116 eq11636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq11636
  have eq12035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq12022
  have eq12039 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12035
       have r₂ := eq28
       grind)
    | exact resolve eq12035 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12035
  have eq12053 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq12039
  have eq12092 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12053
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12053
    | exact resolve eq12053 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12053
  have eq13899 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq12092
       grind)
    | exact superpose eq12092 eq45
    | exact resolve eq45 eq12092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12092
  have eq13919 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq13899
    | exact resolve eq13899 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13899
  have eq14926 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13919 eq10745
    | exact resolve eq10745 eq13919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10745
  have eq14934 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14926
  have eq14942 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14934
       have r₂ := eq10718
       grind)
    | exact resolve eq14934 eq10718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10718 eq14934
  have eq14969 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq14942
  have eq15008 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq14969
    | exact resolve eq14969 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14969
  have eq15400 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15008 eq13919
    | exact resolve eq13919 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13919 eq15008
  have eq15406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15400
  have eq15414 : x = (M.op x y) := by
    first
    | (have r₁ := eq15406
       have r₂ := eq28
       grind)
    | exact resolve eq15406 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15406
  have eq15416 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15414 eq21
    | exact resolve eq21 eq15414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq15423 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq15414 eq75
    | (have r₁ := eq75
       have r₂ := eq15414
       grind)
    | exact resolve eq75 eq15414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq15497 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq15423
  have eq15548 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15416
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15416
    | exact resolve eq15416 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15416
  have eq15684 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15548 eq27
    | exact resolve eq27 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22419 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq15497
       grind)
    | exact superpose eq15497 eq45
    | exact resolve eq45 eq15497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22434 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq533 x y
       have i₂ := eq15497
       grind)
    | exact superpose eq15497 eq533
    | (have j0 := eq533 x y
       grind)
    | exact resolve eq533 eq15497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15497
  have eq22435 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq22434
  have eq22442 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22435
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22435
    | exact resolve eq22435 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22435
  have eq22452 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15548 eq22419
    | exact resolve eq22419 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22419
  have eq22454 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22442
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22442
    | exact resolve eq22442 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22442
  have eq22463 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22452
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22452
    | exact resolve eq22452 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22452
  have eq22464 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq22454
    | exact resolve eq22454 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22454
  have eq22471 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15548 eq22463
    | exact resolve eq22463 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22463
  have eq22472 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15548 eq22464
    | exact resolve eq22464 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22464
  have eq22475 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22472
       have r₂ := eq28
       grind)
    | exact resolve eq22472 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22472
  have eq22478 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22475
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22475
    | exact resolve eq22475 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22475
  have eq22481 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq22478
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22478
    | exact resolve eq22478 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22478
  have eq22484 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15548 eq22481
    | exact resolve eq22481 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22481
  have eq22557 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq22484
  have eq22616 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq15684 eq22557
    | exact resolve eq22557 eq15684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22557
  have eq24441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22616 eq22471
    | exact resolve eq22471 eq22616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22471 eq22616
  have eq24450 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq24441
  have eq24452 : x = (M.op y y) := by
    first
    | (have r₁ := eq24450
       have r₂ := eq28
       grind)
    | exact resolve eq24450 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24450
  have eq24942 : (M.op x y) = (k x y) := by grind
  clear eq24452
  have eq25000 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq24942
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24942
    | exact resolve eq24942 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24942
  have eq25021 : x = (k x y) := by
    first
    | exact superpose eq15414 eq25000
    | exact resolve eq25000 eq15414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15414 eq25000
  have eq26942 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq25021
       grind)
    | exact superpose eq25021 eq45
    | exact resolve eq45 eq25021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq26958 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq533 x y
       have i₂ := eq25021
       grind)
    | exact superpose eq25021 eq533
    | (have j0 := eq533 x y
       grind)
    | exact resolve eq533 eq25021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq25021
  have eq26960 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq26958
  have eq26967 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26960
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26960
    | exact resolve eq26960 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26960
  have eq26977 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15548 eq26942
    | exact resolve eq26942 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942
  have eq26978 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26967
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26967
    | exact resolve eq26967 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26967
  have eq26988 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq26977
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26977
    | exact resolve eq26977 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26977
  have eq26989 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq26978
    | exact resolve eq26978 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq26978
  have eq26997 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15548 eq26988
    | exact resolve eq26988 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26988
  have eq26998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15548 eq26989
    | exact resolve eq26989 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26989
  have eq27002 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq26998
       have r₂ := eq28
       grind)
    | exact resolve eq26998 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26998
  have eq27006 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27002
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27002
    | exact resolve eq27002 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq27002
  have eq27010 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27006
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27006
    | exact resolve eq27006 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq27006
  have eq27014 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq15548 eq27010
    | exact resolve eq27010 eq15548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15548 eq27010
  have eq29570 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq27014
  have eq29628 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15684 eq29570
    | exact resolve eq29570 eq15684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15684 eq29570
  have eq29640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26997 eq29628
    | exact resolve eq29628 eq26997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26997 eq29628
  have eq29641 : False := by grind
  exact eq29641

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq85 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq86
    | (have j0 := eq86 X0
       grind)
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq86
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X0
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq94 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq94 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq94 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq95 (σ X0)
       grind)
    | exact superpose eq95 eq15
    | exact resolve eq15 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq98 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq98
    | exact resolve eq98 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq98
  have eq179 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq16
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq777 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq817 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq777 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq777
    | (have j0 := eq777 X0 X1
       grind)
    | exact resolve eq777 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq179
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq179
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq179
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq179
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq179 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq1019
  have eq9090 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1020
       grind)
    | exact superpose eq1020 eq16
    | exact resolve eq16 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq9091 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq9090
       have r₂ := eq109 x
       grind)
    | exact resolve eq9090 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9090
  have eq9338 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9091
       grind)
    | exact superpose eq9091 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9091
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9091
       grind)
    | exact resolve eq12 eq9091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9091
  have eq9365 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq9338
  have eq9366 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq9365
       grind)
    | exact superpose eq9365 eq179
    | exact resolve eq179 eq9365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq9365
  have eq9386 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq9366
  have eq9387 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9386
  have eq9652 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq9387
       grind)
    | exact superpose eq9387 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9387
       grind)
    | exact resolve eq12 eq9387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9387
  have eq9679 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq9652
  have eq9690 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9679
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9679
    | exact resolve eq9679 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9679
  have eq9696 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9690
       grind)
    | exact superpose eq9690 eq16
    | exact resolve eq16 eq9690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690
  have eq9876 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9696
       have i₂ := eq817 x y
       grind)
    | exact superpose eq817 eq9696
    | (have j1 := eq817 x y
       grind)
    | (have r₁ := eq9696
       have r₂ := eq817 x y
       grind)
    | (have r₁ := eq9696
       have r₂ := eq817 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq9696
       have r₂ := eq817 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq9696 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq9877 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq9876
  have eq9881 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9877
       grind)
    | exact superpose eq9877 eq16
    | exact resolve eq16 eq9877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9877
  have eq9882 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9881
       have r₂ := eq109 x
       grind)
    | exact resolve eq9881 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9881
  have eq10008 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq9882
       grind)
    | exact superpose eq9882 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq9882
       grind)
    | exact resolve eq12 eq9882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9882
  have eq10039 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq10008
  have eq10040 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9696
       have i₂ := eq10039
       grind)
    | exact superpose eq10039 eq9696
    | exact resolve eq9696 eq10039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9696 eq10039
  have eq10065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq10040
  have eq10066 : (σ x) = (σ y) := by grind
  clear eq10065
  have eq10192 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10066
       grind)
    | exact superpose eq10066 eq16
    | exact resolve eq16 eq10066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10193 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10066
       grind)
    | exact superpose eq10066 eq10
    | exact resolve eq10 eq10066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10066
  have eq10269 : x = y := by
    first
    | (have i₁ := eq10193
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq10193
    | exact resolve eq10193 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10193
  have eq10270 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10192
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq10192
    | exact resolve eq10192 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq10192
  have eq10275 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq10270
       have i₂ := eq10269
       grind)
    | exact superpose eq10269 eq10270
    | exact resolve eq10270 eq10269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10269 eq10270
  have eq10276 : False := by grind
  exact eq10276

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq16
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq828 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq865 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq828 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq828
    | (have j0 := eq828 X0 X1
       grind)
    | exact resolve eq828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq1113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq202
       have i₂ := eq865 y x
       grind)
    | exact superpose eq865 eq202
    | (have j1 := eq865 (σ y) (σ x)
       grind)
    | (have r₁ := eq202
       have r₂ := eq865 y x
       grind)
    | (have r₁ := eq202
       have r₂ := eq865 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq202
       have r₂ := eq865 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq202 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1114 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1113
  have eq8766 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1114
       grind)
    | exact superpose eq1114 eq16
    | exact resolve eq16 eq1114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114
  have eq8767 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8766
       have r₂ := eq22 x
       grind)
    | exact resolve eq8766 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8766
  have eq8770 : x ≠ x ∨ x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8767
       grind)
    | exact superpose eq8767 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8767
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8767
       grind)
    | exact resolve eq13 eq8767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8767
  have eq8797 : x = y ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8770
  have eq11259 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8797
       grind)
    | exact superpose eq8797 eq16
    | exact resolve eq16 eq8797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8797
  have eq11260 : x = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11259
       have r₂ := eq22 x
       grind)
    | exact resolve eq11259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11259
  have eq11268 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq208 x y
       have i₂ := eq11260
       grind)
    | exact superpose eq11260 eq208
    | (have j0 := eq208 x y
       grind)
    | exact resolve eq208 eq11260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq11260
  have eq11299 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq11268
  have eq11300 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11299
  have eq11440 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11300
       grind)
    | exact superpose eq11300 eq10
    | exact resolve eq10 eq11300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11300
  have eq11511 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11440
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11440
    | exact resolve eq11440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11440
  have eq11513 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11511
       grind)
    | exact superpose eq11511 eq16
    | exact resolve eq16 eq11511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11511
  have eq11514 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11513
       have r₂ := eq22 x
       grind)
    | exact resolve eq11513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11513
  have eq11654 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11514
       grind)
    | exact superpose eq11514 eq16
    | exact resolve eq16 eq11514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11672 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq11514
       grind)
    | exact superpose eq11514 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11514
       grind)
    | exact resolve eq13 eq11514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11711 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq11672
  have eq11718 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11711
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11711
    | exact resolve eq11711 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11711
  have eq11865 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11514
       have i₂ := eq11718
       grind)
    | exact superpose eq11718 eq11514
    | exact resolve eq11514 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11514
  have eq11867 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11718
       grind)
    | exact superpose eq11718 eq10
    | exact resolve eq10 eq11718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11718
  have eq11938 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11867
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11867
    | exact resolve eq11867 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11867
  have eq11940 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11865
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq11865
    | exact resolve eq11865 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11865
  have eq11943 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq11654
       have i₂ := eq11938
       grind)
    | exact superpose eq11938 eq11654
    | exact resolve eq11654 eq11938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11938
  have eq11944 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq11943
       have r₂ := eq11940
       grind)
    | exact resolve eq11943 eq11940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11940 eq11943
  have eq12109 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq865 y x
       have i₂ := eq11944
       grind)
    | exact superpose eq11944 eq865
    | (have j0 := eq865 y x
       grind)
    | exact resolve eq865 eq11944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq11944
  have eq12185 : x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12109
       have r₂ := eq11654
       grind)
    | exact resolve eq12109 eq11654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12109
  have eq12377 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12185
       grind)
    | exact superpose eq12185 eq16
    | exact resolve eq16 eq12185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12185
  have eq12385 : x = (M.op x y) := by
    first
    | (have r₁ := eq12377
       have r₂ := eq22 x
       grind)
    | exact resolve eq12377 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12377
  have eq12393 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq11654
       have i₂ := eq12385
       grind)
    | exact superpose eq12385 eq11654
    | exact resolve eq11654 eq12385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11654 eq12385
  have eq12442 : False := by grind
  exact eq12442

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_pyx_pyy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq196 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq81 X0 X1
       grind)
    | exact superpose eq81 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq81 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq81 X1 X1
       grind)
    | exact resolve eq13 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq81 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq198 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq199 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq201 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       have j1 := eq197 X0 X1
       grind)
    | (have r₁ := eq201 X0 X1
       have r₂ := eq197 X0 X1
       grind)
    | (have r₁ := eq201 (k X1 X0) X0
       have r₂ := eq197 X0 X1
       grind)
    | (have r₁ := eq201 X0 X0
       have r₂ := eq197 X0 X0
       grind)
    | exact resolve eq201 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq201
  have eq516 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq205
    | exact resolve eq205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq524 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq538 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq516
    | (have j0 := eq516 X0 X1
       grind)
    | exact resolve eq516 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq516
  have eq540 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq538
    | exact resolve eq538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq588 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq540 (τ X0) X1
       grind)
    | exact superpose eq540 eq19
    | (have j1 := eq540 (τ X0) X1
       grind)
    | exact resolve eq19 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq540
  have eq821 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq588 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq588
    | exact resolve eq588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq874 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq821 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq821
    | (have j0 := eq821 X0 X1
       grind)
    | exact resolve eq821 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq971 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq524
       have i₂ := eq874 x y
       grind)
    | exact superpose eq874 eq524
    | (have j1 := eq874 (σ x) (σ y)
       grind)
    | (have r₁ := eq524
       have r₂ := eq874 x y
       grind)
    | exact resolve eq524 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq971
  have eq978 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq972
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq524
       have i₂ := eq978
       grind)
    | exact superpose eq978 eq524
    | exact resolve eq524 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq978
  have eq1018 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1017
  have eq1019 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1018
  have eq1032 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1019
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
  have eq1094 : (σ (M.op x y)) ≠ (σ (k y x)) := by
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
  have eq1131 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1094
       have i₂ := eq874 x y
       grind)
    | exact superpose eq874 eq1094
    | (have j1 := eq874 x y
       grind)
    | (have r₁ := eq1094
       have r₂ := eq874 x y
       grind)
    | exact resolve eq1094 eq874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq1132 : x = (M.op y y) := by grind
  clear eq1131
  have eq1139 : (M.op x y) = (k y x) := by grind
  clear eq1132
  have eq1212 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1094
       have i₂ := eq1139
       grind)
    | exact superpose eq1139 eq1094
    | exact resolve eq1094 eq1139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1139
  have eq1215 : False := by grind
  exact eq1215

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pxy_pyx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq263 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq263 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq263 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq263 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq275 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq264 (σ X0)
       grind)
    | exact superpose eq264 eq15
    | exact resolve eq15 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq264 (τ X0)
       grind)
    | exact superpose eq264 eq31
    | exact resolve eq31 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq281
    | exact resolve eq281 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq264 X0
       grind)
    | exact superpose eq264 eq275
    | exact resolve eq275 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq275
  have eq337 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq9
    | exact resolve eq9 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X1 X1)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X1 (σ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq337
    | exact resolve eq337 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq458 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq367 X0 X0
       have i₂ := eq294 (M.op X0 X0)
       grind)
    | exact superpose eq294 eq367
    | exact resolve eq367 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294 eq367
  have eq479 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq12
    | exact resolve eq12 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq479 X0
       have i₂ := eq15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq15 eq479
    | (have j0 := eq479 X0
       grind)
    | exact resolve eq479 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq526 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq529 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq3712 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq521 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq521
    | (have j0 := eq521 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       grind)
    | exact resolve eq521 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq521 x y
       grind)
    | exact superpose eq521 eq16
    | (have j1 := eq521 x y
       grind)
    | exact resolve eq16 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3727 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3728 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq521 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq3733 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq3712 X0
       have j1 := eq480 X0
       grind)
    | (have r₁ := eq3712 X0
       have r₂ := eq480 X0
       grind)
    | exact resolve eq3712 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3712
  have eq5273 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq529 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq529
    | exact resolve eq529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq5445 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5273 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5273
    | (have j0 := eq5273 X0 X1
       grind)
    | exact resolve eq5273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273
  have eq8188 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq526 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq526
    | exact resolve eq526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq8481 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8188 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq8188
    | (have j0 := eq8188 X0 X1
       grind)
    | exact resolve eq8188 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8188
  have eq8579 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ (M.op (τ X0) (τ X1))) = (τ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8481 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq8481
    | (have j0 := eq8481 (τ X0) (τ X1)
       grind)
    | exact resolve eq8481 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8481
  have eq9508 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3728 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq3728
    | (have j0 := eq3728 (τ X0) (τ X1)
       grind)
    | exact resolve eq3728 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9557 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9508 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9508
    | (have j0 := eq9508 X0 X1
       grind)
    | exact resolve eq9508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9508
  have eq9580 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9557 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9557
    | (have j0 := eq9557 X0 X1
       grind)
    | exact resolve eq9557 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9557
  have eq9602 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9580 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9580
    | (have j0 := eq9580 X0 X1
       grind)
    | exact resolve eq9580 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9580
  have eq9623 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9602 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9602
    | (have j0 := eq9602 X0 X1
       grind)
    | exact resolve eq9602 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9602
  have eq9640 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9623 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9623
    | (have j0 := eq9623 X0 X1
       grind)
    | exact resolve eq9623 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9623
  have eq9653 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9640 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9640
    | (have j0 := eq9640 X0 X1
       grind)
    | exact resolve eq9640 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9640
  have eq9679 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9653 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq9653
    | (have j0 := eq9653 (τ X0) (τ X1)
       grind)
    | exact resolve eq9653 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9653
  have eq19470 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3727 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3727
    | exact resolve eq3727 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq19533 : ∀ X0 X1 : G, (k (σ X1) X0) ≠ (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19470 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq19470
    | (have j0 := eq19470 X0 X1
       grind)
    | exact resolve eq19470 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19470
  have eq19537 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19533 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19533
    | exact resolve eq19533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19533
  have eq20894 : ∀ X0 : G, (σ X0) ≠ (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq13 (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq3733 X0
       grind)
    | exact superpose eq3733 eq13
    | (have j0 := eq13 (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))
       have j1 := eq3733 X0
       grind)
    | exact resolve eq13 eq3733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733
  have eq20898 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq20894 X0
       grind)
    | (have r₁ := eq20894 X0
       have r₂ := eq458 X0
       grind)
    | exact resolve eq20894 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20894
  have eq20908 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq20898 X0
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq20898
    | (have j0 := eq20898 X0
       grind)
    | exact resolve eq20898 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458 eq20898
  have eq20915 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq20908 X0
       have j1 := eq480 X0
       grind)
    | (have r₁ := eq20908 X0
       have r₂ := eq480 X0
       grind)
    | exact resolve eq20908 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq20908
  have eq20922 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq20915 X0
       have i₂ := eq15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq15 eq20915
    | (have j0 := eq20915 X0
       grind)
    | exact resolve eq20915 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20915
  have eq20923 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have j0 := eq20922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20922
  have eq20961 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq20923 X0
       grind)
    | exact superpose eq20923 eq10
    | exact resolve eq10 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20962 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1
       have i₂ := eq20923 X0
       grind)
    | exact superpose eq20923 eq15
    | exact resolve eq15 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20963 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))
       have i₂ := eq20923 X0
       grind)
    | exact superpose eq20923 eq15
    | exact resolve eq15 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21186 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20963 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20963
    | exact resolve eq20963 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20963
  have eq21187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20962 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq20962
    | exact resolve eq20962 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20962
  have eq21188 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq20961 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq20961
    | exact resolve eq20961 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20961
  have eq888079 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X1) (τ X0)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) (τ X1)
       have i₂ := eq8579 X0 X1
       grind)
    | exact superpose eq8579 eq12
    | (have j1 := eq8579 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) (τ X1)
       have r₂ := eq8579 X0 X1
       grind)
    | exact resolve eq12 eq8579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579
  have eq888094 : ∀ X0 X1 : G, (τ X0) = (k (τ X1) (τ X0)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ (τ (k X1 X0))) = (τ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq888079 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888079
  have eq888105 : ∀ X0 X1 : G, (τ (τ (k X1 X0))) = (τ (M.op (τ X1) (τ X0))) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq888094 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq888094
    | (have j0 := eq888094 X0 X1
       grind)
    | exact resolve eq888094 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888094
  have eq888356 : ∀ X0 X1 : G, (τ (τ (k X1 (σ X0)))) = (τ (M.op (τ X1) X0)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq888105 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq888105
    | exact resolve eq888105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888105
  have eq890425 : ∀ X0 X1 : G, (τ (k (τ X1) X0)) = (τ (M.op (τ X1) X0)) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ (k X1 (σ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq888356 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq888356
    | (have j0 := eq888356 X0 X1
       grind)
    | exact resolve eq888356 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888356
  have eq890442 : ∀ X0 X1 : G, (τ (k (τ X1) X0)) = (τ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq890425 X0 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq890425
    | (have j0 := eq890425 X0 X1
       grind)
    | exact resolve eq890425 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890425
  have eq890466 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq890442 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq890442
    | exact resolve eq890442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890442
  have eq893191 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq890466 X0 (σ X1)
       grind)
    | exact superpose eq890466 eq22
    | (have j1 := eq890466 X0 (σ X1)
       grind)
    | exact resolve eq22 eq890466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq893260 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq890466 X0 X1
       grind)
    | exact superpose eq890466 eq11
    | (have j1 := eq890466 X0 X1
       grind)
    | exact resolve eq11 eq890466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890466
  have eq895255 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq893260 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq893260
    | (have j0 := eq893260 X0 X1
       grind)
    | exact resolve eq893260 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893260
  have eq896839 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1)) ∨ (k (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1) = X1 ∨ (M.op (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1) = (M.op X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq21187 X0 X1
       have i₂ := eq895255 (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1
       grind)
    | exact superpose eq895255 eq21187
    | (have j1 := eq895255 (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1
       grind)
    | exact resolve eq21187 eq895255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21187
  have eq897581 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1) = X1 ∨ (M.op (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1) = (M.op X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq896839 X0 X1
       have i₂ := eq21188 X0
       grind)
    | exact superpose eq21188 eq896839
    | (have j0 := eq896839 X0 X1
       grind)
    | exact resolve eq896839 eq21188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896839
  have eq897692 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) X1) = (M.op X1 (k X0 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq897581 X0 X1
       have i₂ := eq21188 X0
       grind)
    | exact superpose eq21188 eq897581
    | (have j0 := eq897581 X0 X1
       grind)
    | exact resolve eq897581 eq21188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897581
  have eq897716 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq897692 X0 X1
       have i₂ := eq21188 X0
       grind)
    | exact superpose eq21188 eq897692
    | (have j0 := eq897692 X0 X1
       grind)
    | exact resolve eq897692 eq21188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897692
  have eq906271 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq893191 X1 X0
       grind)
    | exact superpose eq893191 eq22
    | (have j1 := eq893191 X1 X0
       grind)
    | exact resolve eq22 eq893191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq893191
  have eq907306 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq906271 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq906271
    | (have j0 := eq906271 X0 X1
       grind)
    | exact resolve eq906271 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906271
  have eq907663 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) ∨ (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq907306 (τ X0) X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq907306
    | (have j0 := eq907306 (τ X1) X0
       grind)
    | exact resolve eq907306 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907306
  have eq909715 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq907663 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq907663
    | (have j0 := eq907663 X0 X1
       grind)
    | exact resolve eq907663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907663
  have eq910418 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq909715 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq909715
    | (have j0 := eq909715 X0 X1
       grind)
    | exact resolve eq909715 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909715
  have eq912868 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq910418 X0 X1
       grind)
    | exact superpose eq910418 eq11
    | (have j1 := eq910418 X0 X1
       grind)
    | exact resolve eq11 eq910418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq913962 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq910418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910418
  have eq914862 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq912868 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq912868
    | (have j0 := eq912868 X0 X1
       grind)
    | exact resolve eq912868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912868
  have eq915896 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq914862 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq914862
    | (have j0 := eq914862 (σ X0) (σ X1)
       grind)
    | exact resolve eq914862 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916286 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X2)) = (τ (k (k X1 X0) X2)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (k X1 X0)
       have i₂ := eq914862 X1 X0
       grind)
    | exact superpose eq914862 eq31
    | (have j1 := eq914862 X0 X1
       grind)
    | exact resolve eq31 eq914862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914862
  have eq918307 : ∀ X0 X1 X2 : G, (τ (k X0 X2)) = (τ (k (k X1 X0) X2)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq916286 X0 X1 X2
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq916286
    | (have j0 := eq916286 X0 X1 X2
       grind)
    | exact resolve eq916286 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916286
  have eq918388 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq915896 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq915896
    | (have j0 := eq915896 X0 X1
       grind)
    | exact resolve eq915896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915896
  have eq918464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq918388 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq918388
    | (have j0 := eq918388 X0 X1
       grind)
    | exact resolve eq918388 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918388
  have eq921766 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (k X2 X0) X1) ∨ (M.op X0 X2) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (k X2 X0) X1)
       have i₂ := eq918307 X0 X2 X1
       grind)
    | exact superpose eq918307 eq11
    | (have j1 := eq918307 X0 X2 X2
       grind)
    | exact resolve eq11 eq918307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918307
  have eq923782 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (k X2 X0) X1) ∨ (M.op X0 X2) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq921766 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq921766
    | (have j0 := eq921766 X0 X1 X2
       grind)
    | exact resolve eq921766 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921766
  have eq925849 : ∀ X0 X1 X2 : G, (σ (k X0 (k X1 (M.op (M.op X1 X1) (M.op X1 X1))))) = (σ (k (k X2 X0) X1)) ∨ (M.op X0 X2) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21186 X1 (k X2 X0)
       have i₂ := eq923782 X0 (k X1 (M.op (M.op X1 X1) (M.op X1 X1))) X2
       grind)
    | exact superpose eq923782 eq21186
    | (have j1 := eq923782 X0 X1 X2
       grind)
    | exact resolve eq21186 eq923782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923782
  have eq926164 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (k (k X2 X0) X1)) ∨ (M.op X0 X2) = (M.op X2 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq925849 X0 X1 X2
       have i₂ := eq21186 X1 X0
       grind)
    | exact superpose eq21186 eq925849
    | (have j0 := eq925849 X0 X1 X2
       grind)
    | exact resolve eq925849 eq21186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21186 eq925849
  have eq961444 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq918464 x y
       grind)
    | exact superpose eq918464 eq16
    | (have j1 := eq918464 x y
       grind)
    | exact resolve eq16 eq918464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918464
  have eq961797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ y = (k x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq961444
       have i₂ := eq897716 x y
       grind)
    | exact superpose eq897716 eq961444
    | (have j1 := eq897716 x y
       grind)
    | (have r₁ := eq961444
       have r₂ := eq897716 x y
       grind)
    | exact resolve eq961444 eq897716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897716
  have eq961800 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq961797
  have eq961801 : (M.op x y) = (M.op y x) ∨ y = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq961800
  have eq961807 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq961801
       grind)
    | exact superpose eq961801 eq12
    | exact resolve eq12 eq961801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961808 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq961801
       grind)
    | exact superpose eq961801 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq961801
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq961801
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq961801
       grind)
    | exact resolve eq13 eq961801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961801
  have eq961811 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (k x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq961808
  have eq961813 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq961807
       have r₂ := eq961811
       grind)
    | exact resolve eq961807 eq961811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961807 eq961811
  have eq964284 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq961813
       grind)
    | exact superpose eq961813 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq961813
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq961813
       grind)
    | exact resolve eq13 eq961813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961813
  have eq964285 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq964284
  have eq964287 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq964285
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq964285 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964285
  have eq964292 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq964287
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq964287
    | exact resolve eq964287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964287
  have eq964300 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq964292
       grind)
    | exact superpose eq964292 eq16
    | exact resolve eq16 eq964292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964292
  have eq964432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq964300
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq964300
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq964300 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964300
  have eq964438 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq964432
  have eq964439 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq964438
  have eq964955 : (τ y) ≠ (τ y) ∨ y = (M.op y x) ∨ (τ y) = (τ (k x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq913962 x y
       have i₂ := eq964439
       grind)
    | exact superpose eq964439 eq913962
    | (have j0 := eq913962 x y
       grind)
    | exact resolve eq913962 eq964439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq964956 : y = (M.op y x) ∨ (τ y) = (τ (k x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq964955
  have eq971938 : y ≠ (M.op x y) ∨ (τ y) = (τ (k x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq964956
  have eq971943 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq971938
       have r₂ := eq964439
       grind)
    | exact resolve eq971938 eq964439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964439 eq971938
  have eq971965 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq971943
       grind)
    | exact superpose eq971943 eq12
    | exact resolve eq12 eq971943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971966 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq971943
       grind)
    | exact superpose eq971943 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq971943
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq971943
       grind)
    | exact resolve eq13 eq971943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971943
  have eq971969 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq971966
  have eq971970 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq971969
  have eq971971 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq971965
  have eq971974 : (M.op x y) = (k y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq971971
       have r₂ := eq971970
       grind)
    | exact resolve eq971971 eq971970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971971
  have eq972045 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq19537 y x
       have i₂ := eq971974
       grind)
    | exact superpose eq971974 eq19537
    | (have j0 := eq19537 x y
       grind)
    | (have r₁ := eq19537 y x
       have r₂ := eq971974
       grind)
    | exact resolve eq19537 eq971974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19537
  have eq972225 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq895255 y x
       have i₂ := eq971974
       grind)
    | exact superpose eq971974 eq895255
    | (have j0 := eq895255 x y
       grind)
    | exact resolve eq895255 eq971974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895255
  have eq972257 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq972225
  have eq972258 : x = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq972045
  have eq972360 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq972258
  have eq972370 : (M.op x y) = (M.op y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq972360
       have r₂ := eq972257
       grind)
    | exact resolve eq972360 eq972257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972257 eq972360
  have eq972376 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq972370
       grind)
    | exact superpose eq972370 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq972370
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq972370
       grind)
    | exact resolve eq13 eq972370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972377 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq972376
  have eq972381 : (M.op x y) = (k x y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq972377
       have r₂ := eq12 x y
       grind)
    | exact resolve eq972377 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972377
  have eq972383 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq961444
       have i₂ := eq972381
       grind)
    | exact superpose eq972381 eq961444
    | exact resolve eq961444 eq972381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961444
  have eq972388 : (τ y) ≠ (τ (M.op x y)) ∨ (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) ∨ (τ y) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq9679 x y
       have i₂ := eq972381
       grind)
    | exact superpose eq972381 eq9679
    | (have j0 := eq9679 x y
       grind)
    | (have r₁ := eq9679 x y
       have r₂ := eq972381
       grind)
    | exact resolve eq9679 eq972381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972404 : y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq972383
  have eq972406 : (τ y) ≠ (τ (M.op x y)) ∨ (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) ∨ (τ y) = (M.op (τ x) (τ y)) := by
    first
    | (have j1 := eq9679 x y
       grind)
    | (have r₁ := eq972388
       have r₂ := eq9679 x y
       grind)
    | exact resolve eq972388 eq9679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972388
  have eq972758 : (τ y) ≠ (τ y) ∨ y = (M.op y x) ∨ (τ y) = (τ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq913962 x y
       have i₂ := eq972404
       grind)
    | exact superpose eq972404 eq913962
    | (have j0 := eq913962 (σ x) (σ y)
       grind)
    | exact resolve eq913962 eq972404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913962 eq972404
  have eq972759 : (τ y) ≠ (τ y) ∨ y = (M.op y x) ∨ (τ y) = (τ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq972758
  have eq972760 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by grind
  clear eq972759
  have eq972775 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq972760
       grind)
    | exact superpose eq972760 eq12
    | exact resolve eq12 eq972760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972776 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq972760
       grind)
    | exact superpose eq972760 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq972760
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq972760
       grind)
    | exact resolve eq13 eq972760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972777 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq972760
       grind)
    | exact superpose eq972760 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq972760
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq972760
       grind)
    | exact resolve eq13 eq972760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972760
  have eq972778 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by grind
  clear eq972777
  have eq972779 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by grind
  clear eq972776
  have eq972780 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq972778
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq972778 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972778
  have eq972781 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq972779
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq972779
    | exact resolve eq972779 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972779
  have eq972782 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq972775
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq972775
    | exact resolve eq972775 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972775
  have eq972785 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq972780
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq972780
    | exact resolve eq972780 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972780
  have eq972786 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq972782
       have r₂ := eq972781
       grind)
    | exact resolve eq972782 eq972781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972781 eq972782
  have eq972795 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq972785
       grind)
    | exact superpose eq972785 eq16
    | exact resolve eq16 eq972785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972785
  have eq972925 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (τ y) = (τ (M.op x y)) ∨ y = (M.op y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq972795
       have i₂ := eq972381
       grind)
    | exact superpose eq972381 eq972795
    | exact resolve eq972795 eq972381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972381 eq972795
  have eq972937 : y = (M.op y x) ∨ (τ y) = (τ (M.op x y)) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq972925
  have eq972985 : y = (M.op x y) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (M.op x y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq972370
       have i₂ := eq972937
       grind)
    | exact superpose eq972937 eq972370
    | exact resolve eq972370 eq972937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972937
  have eq973009 : y = (M.op x y) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (M.op x y)) := by grind
  clear eq972985
  have eq973031 : y ≠ y ∨ y = (k x y) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq973009
       grind)
    | exact superpose eq973009 eq12
    | (have r₁ := eq12 x y
       have r₂ := eq973009
       grind)
    | exact resolve eq12 eq973009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973009
  have eq973049 : y = (k x y) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (M.op x y)) := by grind
  clear eq973031
  have eq973088 : (τ y) ≠ (τ y) ∨ (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) ∨ (τ y) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq9679 x y
       have i₂ := eq973049
       grind)
    | exact superpose eq973049 eq9679
    | (have j0 := eq9679 x y
       grind)
    | (have r₁ := eq9679 x y
       have r₂ := eq973049
       grind)
    | exact resolve eq9679 eq973049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973049
  have eq973171 : (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) ∨ (τ y) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (M.op x y)) := by grind
  clear eq973088
  have eq973262 : (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) ∨ (τ y) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (M.op x y)) := by
    first
    | (have j1 := eq9679 x y
       grind)
    | (have r₁ := eq973171
       have r₂ := eq9679 x y
       grind)
    | exact resolve eq973171 eq9679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9679 eq973171
  have eq973290 : (τ y) = (M.op (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) := by
    first
    | (have r₁ := eq973262
       have r₂ := eq972406
       grind)
    | exact resolve eq973262 eq972406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972406 eq973262
  have eq973866 : (τ y) ≠ (τ y) ∨ (τ y) = (k (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) := by
    first
    | (have i₁ := eq12 (τ x) (τ y)
       have i₂ := eq973290
       grind)
    | exact superpose eq973290 eq12
    | (have r₁ := eq12 (τ x) (τ y)
       have r₂ := eq973290
       grind)
    | exact resolve eq12 eq973290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973290
  have eq973883 : (τ y) = (k (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) := by grind
  clear eq973866
  have eq973896 : (M.op (τ x) (τ y)) = (M.op (τ y) (τ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq973883
       have i₂ := eq31 y x
       grind)
    | exact superpose eq31 eq973883
    | exact resolve eq973883 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973883
  have eq973938 : (τ x) ≠ (M.op (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (k (τ y) (τ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq12 (τ y) (τ x)
       have i₂ := eq973896
       grind)
    | exact superpose eq973896 eq12
    | exact resolve eq12 eq973896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973939 : (M.op (τ x) (τ y)) ≠ (M.op (τ x) (τ y)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (k (τ y) (τ x)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq13 (τ y) (τ x)
       have i₂ := eq973896
       grind)
    | exact superpose eq973896 eq13
    | (have j0 := eq13 (τ y) (τ x)
       grind)
    | (have r₁ := eq13 (τ x) (τ y)
       have r₂ := eq973896
       grind)
    | (have r₁ := eq13 (τ y) (τ x)
       have r₂ := eq973896
       grind)
    | exact resolve eq13 eq973896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973940 : (M.op (τ x) (τ y)) ≠ (M.op (τ x) (τ y)) ∨ (τ y) = (M.op (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (k (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq13 (τ x) (τ y)
       have i₂ := eq973896
       grind)
    | exact superpose eq973896 eq13
    | (have j0 := eq13 (τ x) (τ y)
       grind)
    | (have r₁ := eq13 (τ x) (τ y)
       have r₂ := eq973896
       grind)
    | (have r₁ := eq13 (τ y) (τ x)
       have r₂ := eq973896
       grind)
    | exact resolve eq13 eq973896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973896
  have eq973941 : (τ y) = (M.op (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (k (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq973940
  have eq973942 : (τ x) = (M.op (τ x) (τ y)) ∨ (M.op (τ x) (τ y)) = (k (τ y) (τ x)) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq973939
  have eq973943 : (M.op (τ x) (τ y)) = (k (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have j1 := eq12 (τ x) (τ y)
       grind)
    | (have r₁ := eq973941
       have r₂ := eq12 (τ x) (τ y)
       grind)
    | exact resolve eq973941 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973941
  have eq973944 : (τ (k y x)) = (M.op (τ x) (τ y)) ∨ (τ x) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq973942
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq973942
    | exact resolve eq973942 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973942
  have eq973945 : (τ (k y x)) = (M.op (τ x) (τ y)) ∨ (τ x) ≠ (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq973938
       have i₂ := eq31 x y
       grind)
    | exact superpose eq31 eq973938
    | exact resolve eq973938 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973938
  have eq973948 : (τ (k x y)) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq973943
       have i₂ := eq31 y x
       grind)
    | exact superpose eq31 eq973943
    | exact resolve eq973943 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq973943
  have eq973949 : (τ (k y x)) = (M.op (τ x) (τ y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq973945
       have r₂ := eq973944
       grind)
    | exact resolve eq973945 eq973944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973944 eq973945
  have eq974035 : (τ (k y x)) = (τ (k x y)) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq973948
       have i₂ := eq973949
       grind)
    | exact superpose eq973949 eq973948
    | exact resolve eq973948 eq973949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973948 eq973949
  have eq974075 : (τ y) = (τ (k x y)) ∨ (τ (k y x)) = (τ (k x y)) := by grind
  clear eq974035
  have eq974220 : (τ (M.op (k x y) (k x y))) = (M.op (τ y) (τ y)) ∨ (τ (k y x)) = (τ (k x y)) := by
    first
    | (have i₁ := eq288 (k x y)
       have i₂ := eq974075
       grind)
    | exact superpose eq974075 eq288
    | exact resolve eq288 eq974075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974075
  have eq976104 : (τ (k y x)) = (τ (k x y)) ∨ (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq974220
       have i₂ := eq288 y
       grind)
    | exact superpose eq288 eq974220
    | exact resolve eq974220 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974220
  have eq997506 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq972786
       grind)
    | exact superpose eq972786 eq16
    | exact resolve eq16 eq972786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972786
  have eq997684 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq997506
       have i₂ := eq971974
       grind)
    | exact superpose eq971974 eq997506
    | exact resolve eq997506 eq971974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971974 eq997506
  have eq997698 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (τ y) = (τ (k x y)) ∨ y = (M.op y x) := by grind
  clear eq997684
  have eq997699 : y = (M.op y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq997698
  have eq997751 : y = (M.op x y) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq972370
       have i₂ := eq997699
       grind)
    | exact superpose eq997699 eq972370
    | exact resolve eq972370 eq997699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972370
  have eq997752 : x ≠ y ∨ y = (k y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq997699
       grind)
    | exact superpose eq997699 eq12
    | exact resolve eq12 eq997699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997699
  have eq997775 : y = (M.op x y) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq997751
  have eq997793 : x = y ∨ y = (k y x) ∨ (τ y) = (τ (k x y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq971970
       have i₂ := eq997775
       grind)
    | exact superpose eq997775 eq971970
    | exact resolve eq971970 eq997775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971970 eq997775
  have eq997815 : x = y ∨ y = (k y x) ∨ (τ y) = (τ (k x y)) := by grind
  clear eq997793
  have eq997818 : y = (k y x) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have r₁ := eq997815
       have r₂ := eq997752
       grind)
    | exact resolve eq997815 eq997752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997752 eq997815
  have eq1008252 : (τ y) = (τ (k x y)) ∨ (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) ∨ (τ y) = (τ (k x y)) := by
    first
    | (have i₁ := eq976104
       have i₂ := eq997818
       grind)
    | exact superpose eq997818 eq976104
    | exact resolve eq976104 eq997818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976104 eq997818
  have eq1009416 : (τ y) = (τ (k x y)) ∨ (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) := by grind
  clear eq1008252
  have eq1010408 : (τ (M.op (k x y) (k x y))) = (M.op (τ y) (τ y)) ∨ (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq288 (k x y)
       have i₂ := eq1009416
       grind)
    | exact superpose eq1009416 eq288
    | exact resolve eq288 eq1009416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009416
  have eq1012293 : (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) ∨ (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq1010408
       have i₂ := eq288 y
       grind)
    | exact superpose eq288 eq1010408
    | exact resolve eq1010408 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq1010408
  have eq1012294 : (τ (M.op (k x y) (k x y))) = (τ (M.op y y)) := by grind
  clear eq1012293
  have eq1012604 : (M.op (k x y) (k x y)) = (σ (τ (M.op y y))) := by
    first
    | (have i₁ := eq11 (M.op (k x y) (k x y))
       have i₂ := eq1012294
       grind)
    | exact superpose eq1012294 eq11
    | exact resolve eq11 eq1012294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012294
  have eq1014594 : (M.op (k x y) (k x y)) = (M.op y y) := by
    first
    | (have i₁ := eq1012604
       have i₂ := eq11 (M.op y y)
       grind)
    | exact superpose eq11 eq1012604
    | exact resolve eq1012604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012604
  have eq1015149 : (k x y) = (k (k x y) (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq21188 (k x y)
       have i₂ := eq1014594
       grind)
    | exact superpose eq1014594 eq21188
    | exact resolve eq21188 eq1014594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21188 eq1014594
  have eq1015340 : (σ (k x y)) = (σ (k y (M.op (M.op y y) (M.op y y)))) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq926164 y (M.op (M.op y y) (M.op y y)) x
       have i₂ := eq1015149
       grind)
    | exact superpose eq1015149 eq926164
    | (have j0 := eq926164 x x y
       grind)
    | exact resolve eq926164 eq1015149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926164 eq1015149
  have eq1015622 : (M.op x y) = (M.op y x) ∨ (σ y) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1015340
       have i₂ := eq20923 y
       grind)
    | exact superpose eq20923 eq1015340
    | exact resolve eq1015340 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20923 eq1015340
  have eq1032430 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1015622
       grind)
    | exact superpose eq1015622 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1015622
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1015622
       grind)
    | exact resolve eq13 eq1015622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015622
  have eq1032431 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1032430
  have eq1032432 : y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1032431
  have eq1032434 : (M.op x y) = (k x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1032432
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1032432 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032432
  have eq1032440 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq3723
       have i₂ := eq1032434
       grind)
    | exact superpose eq1032434 eq3723
    | exact resolve eq3723 eq1032434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723
  have eq1032532 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq1032440
  have eq1032534 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3728 x y
       grind)
    | (have r₁ := eq1032532
       have r₂ := eq3728 x y
       grind)
    | exact resolve eq1032532 eq3728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728 eq1032532
  have eq1033393 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1032534
       grind)
    | exact superpose eq1032534 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1032534
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1032534
       grind)
    | exact resolve eq13 eq1032534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032534
  have eq1033394 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1033393
  have eq1033395 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1033394
  have eq1033397 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1033395
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq1033395 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033395
  have eq1033402 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1033397
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1033397
    | exact resolve eq1033397 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033397
  have eq1034258 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1033402
       grind)
    | exact superpose eq1033402 eq16
    | exact resolve eq16 eq1033402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033402
  have eq1034423 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq1034258
       have i₂ := eq1032434
       grind)
    | exact superpose eq1032434 eq1034258
    | exact resolve eq1034258 eq1032434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032434
  have eq1034431 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1034258
       have i₂ := eq5445 x y
       grind)
    | exact superpose eq5445 eq1034258
    | (have j1 := eq5445 x y
       grind)
    | (have r₁ := eq1034258
       have r₂ := eq5445 x y
       grind)
    | exact resolve eq1034258 eq5445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq1034432 : y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1034431
  have eq1034437 : (σ y) = (σ (k x y)) := by grind
  clear eq1034423
  have eq1034461 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1034258
       have i₂ := eq1034437
       grind)
    | exact superpose eq1034437 eq1034258
    | exact resolve eq1034258 eq1034437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034258
  have eq1034508 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1034437
       grind)
    | exact superpose eq1034437 eq10
    | exact resolve eq10 eq1034437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034437
  have eq1035003 : y = (k x y) := by
    first
    | (have i₁ := eq1034508
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1034508
    | exact resolve eq1034508 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034508
  have eq1043995 : (σ y) ≠ (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq1034461
       have i₂ := eq1034432
       grind)
    | exact superpose eq1034432 eq1034461
    | exact resolve eq1034461 eq1034432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034432
  have eq1044014 : (M.op x y) = (M.op y x) := by grind
  clear eq1043995
  have eq1044030 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1044014
       grind)
    | exact superpose eq1044014 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1044014
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1044014
       grind)
    | exact resolve eq13 eq1044014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044014
  have eq1044031 : y = (M.op x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq1044030
  have eq1044033 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq1044031
       have r₂ := eq12 x y
       grind)
    | exact resolve eq1044031 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044031
  have eq1044035 : y = (M.op x y) := by
    first
    | (have i₁ := eq1044033
       have i₂ := eq1035003
       grind)
    | exact superpose eq1035003 eq1044033
    | exact resolve eq1044033 eq1035003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035003 eq1044033
  have eq1044042 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1034461
       have i₂ := eq1044035
       grind)
    | exact superpose eq1044035 eq1034461
    | exact resolve eq1034461 eq1044035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034461 eq1044035
  have eq1044061 : False := by grind
  exact eq1044061
