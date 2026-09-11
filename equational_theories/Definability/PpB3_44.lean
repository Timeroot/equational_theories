import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq271 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 (σ X0) (σ X1)
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X1 X0
       have i₂ := eq271 X1 X0
       grind)
    | exact superpose eq271 eq272
    | (have j0 := eq272 X1 X0
       have j1 := eq271 (σ X1) (σ X0)
       grind)
    | exact resolve eq272 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq412 x y
       grind)
    | exact superpose eq412 eq16
    | (have j1 := eq412 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq412 x y
       grind)
    | exact resolve eq16 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq2703 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2690
  have eq2714 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2703
       grind)
    | exact superpose eq2703 eq16
    | exact resolve eq16 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2717 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2703
       grind)
    | exact superpose eq2703 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2703
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2703
       grind)
    | exact resolve eq13 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2723 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2717
  have eq2725 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2723
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2723
    | exact resolve eq2723 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2723
  have eq2727 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271 eq2725
    | (have j1 := eq271 y x
       grind)
    | exact resolve eq2725 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2728 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2727
       have r₂ := eq2714
       grind)
    | exact resolve eq2727 eq2714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2735 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2728
       grind)
    | exact superpose eq2728 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2728
       grind)
    | exact resolve eq12 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728
  have eq2742 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2735
  have eq2749 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2742
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2742
    | exact resolve eq2742 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2757 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2703 eq2749
    | exact resolve eq2749 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2703 eq2749
  have eq2760 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271 eq2757
    | (have j1 := eq271 y x
       grind)
    | exact resolve eq2757 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq2757
  have eq2761 : x = (M.op x y) := by
    first
    | (have r₁ := eq2760
       have r₂ := eq2714
       grind)
    | exact resolve eq2760 eq2714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2714 eq2760
  have eq2762 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2761
       grind)
    | exact superpose eq2761 eq16
    | exact resolve eq16 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2765 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2761
       grind)
    | exact superpose eq2761 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2761
       grind)
    | exact resolve eq13 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2771 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq2765
  have eq2786 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq272 y x
       have i₂ := eq2771
       grind)
    | exact superpose eq2771 eq272
    | (have j0 := eq272 y x
       grind)
    | exact resolve eq272 eq2771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2789 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq2786
  have eq2794 : x = (M.op y x) := by
    first
    | (have r₁ := eq2789
       have r₂ := eq2762
       grind)
    | exact resolve eq2789 eq2762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq2798 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2794
       grind)
    | exact superpose eq2794 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2794
       grind)
    | exact resolve eq12 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2805 : (M.op x y) = (k y x) := by grind
  clear eq2798
  have eq2812 : x = (k y x) := by
    first
    | (have i₁ := eq2805
       have i₂ := eq2761
       grind)
    | exact superpose eq2761 eq2805
    | exact resolve eq2805 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761 eq2805
  have eq2820 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq272 y x
       have i₂ := eq2812
       grind)
    | exact superpose eq2812 eq272
    | (have j0 := eq272 y x
       grind)
    | exact resolve eq272 eq2812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq2812
  have eq2823 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2820
  have eq2828 : False := by grind
  exact eq2828

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X0) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X1) X0) ≠ X0 ∨ (M.op X0 (M.op (M.op (M.op X1 X0) X1) X0)) = (k X0 (M.op (M.op (M.op X1 X0) X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X0) X1) X0)
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X1 X0) X1) X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq707 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90 x y
       grind)
    | exact superpose eq90 eq16
    | (have j1 := eq90 x y
       grind)
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2419 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq63 X0 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq63
    | (have j1 := eq65 X0
       grind)
    | (have r₁ := eq63 X0 X0
       have r₂ := eq65 X0
       grind)
    | exact resolve eq63 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq65
  have eq2420 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2419 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2419
  have eq2421 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2420 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2420
  have eq2460 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2421 (σ X0)
       grind)
    | exact superpose eq2421 eq15
    | exact resolve eq15 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2479 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2460 X0
       have i₂ := eq2421 X0
       grind)
    | exact superpose eq2421 eq2460
    | exact resolve eq2460 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421 eq2460
  have eq5203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5264 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5203 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5203
    | (have j0 := eq5203 X0 X1
       grind)
    | exact resolve eq5203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5203
  have eq20347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq707
       have i₂ := eq5264 x y
       grind)
    | exact superpose eq5264 eq707
    | (have j1 := eq5264 (σ x) (σ y)
       grind)
    | (have r₁ := eq707
       have r₂ := eq5264 x y
       grind)
    | (have r₁ := eq707
       have r₂ := eq5264 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq707
       have r₂ := eq5264 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq707 eq5264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20348 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq20347
  have eq22478 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20348
       grind)
    | exact superpose eq20348 eq16
    | exact resolve eq16 eq20348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20348
  have eq22479 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq22478
       have r₂ := eq2479 x
       grind)
    | exact resolve eq22478 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22478
  have eq22481 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq22479
       grind)
    | exact superpose eq22479 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22479
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22479
       grind)
    | exact resolve eq12 eq22479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22479
  have eq22485 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq22481
  have eq22486 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq707
       have i₂ := eq22485
       grind)
    | exact superpose eq22485 eq707
    | exact resolve eq707 eq22485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707 eq22485
  have eq22487 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq22486
  have eq22488 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq22487
  have eq22493 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq22488
       grind)
    | exact superpose eq22488 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq22488
       grind)
    | exact resolve eq12 eq22488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22488
  have eq22497 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq22493
  have eq22504 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22497
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq22497
    | exact resolve eq22497 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22497
  have eq22514 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22504
       grind)
    | exact superpose eq22504 eq16
    | exact resolve eq16 eq22504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22504
  have eq22550 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq22514
       have i₂ := eq5264 x y
       grind)
    | exact superpose eq5264 eq22514
    | (have j1 := eq5264 x y
       grind)
    | (have r₁ := eq22514
       have r₂ := eq5264 x y
       grind)
    | (have r₁ := eq22514
       have r₂ := eq5264 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq22514
       have r₂ := eq5264 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq22514 eq5264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5264
  have eq22551 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq22550
  have eq22555 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22551
       grind)
    | exact superpose eq22551 eq16
    | exact resolve eq16 eq22551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22551
  have eq22556 : y = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq22555
       have r₂ := eq2479 x
       grind)
    | exact resolve eq22555 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22555
  have eq22558 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq22556
       grind)
    | exact superpose eq22556 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq22556
       grind)
    | exact resolve eq12 eq22556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22556
  have eq22562 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq22558
  have eq22563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22514
       have i₂ := eq22562
       grind)
    | exact superpose eq22562 eq22514
    | exact resolve eq22514 eq22562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22514 eq22562
  have eq22567 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq22563
  have eq22568 : (σ x) = (σ y) := by grind
  clear eq22567
  have eq22569 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22568
       grind)
    | exact superpose eq22568 eq16
    | exact resolve eq16 eq22568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22570 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22568
       grind)
    | exact superpose eq22568 eq10
    | exact resolve eq10 eq22568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22568
  have eq22634 : x = y := by
    first
    | (have i₁ := eq22570
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22570
    | exact resolve eq22570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22570
  have eq22635 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22569
       have i₂ := eq2479 x
       grind)
    | exact superpose eq2479 eq22569
    | exact resolve eq22569 eq2479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479 eq22569
  have eq22641 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq22635
       have i₂ := eq22634
       grind)
    | exact superpose eq22634 eq22635
    | exact resolve eq22635 eq22634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22634 eq22635
  have eq22642 : False := by grind
  exact eq22642

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq250 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq433 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq250 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq250 X0 X1
       grind)
    | exact superpose eq250 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq250 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq250 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq250 X0 X1
       grind)
    | exact resolve eq13 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq438 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq439 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq438 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq444 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq439
    | (have j0 := eq439 X0 X1
       grind)
    | exact resolve eq439 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq445 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq460 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq445 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq445
    | (have j0 := eq445 (τ X1) (τ X0)
       grind)
    | exact resolve eq445 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq498 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq460 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq460
    | (have j0 := eq460 X0 X1
       grind)
    | exact resolve eq460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq515 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq498 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq498
    | (have j0 := eq498 X0 X1
       grind)
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq520 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq515
    | (have j0 := eq515 X0 X1
       grind)
    | exact resolve eq515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq525 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq520
    | (have j0 := eq520 X0 X1
       grind)
    | exact resolve eq520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq530 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq537 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq445 X0 X1
       have i₂ := eq530 X1 X0
       grind)
    | exact superpose eq530 eq445
    | (have j0 := eq445 X0 X1
       have j1 := eq530 (σ X1) (σ X0)
       grind)
    | exact resolve eq445 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6793 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq537 x y
       grind)
    | exact superpose eq537 eq16
    | (have j1 := eq537 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq537 x y
       grind)
    | exact resolve eq16 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq6822 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6793
  have eq6856 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq6822
  have eq6869 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6856
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6856
    | exact resolve eq6856 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6856
  have eq6879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq530 eq6869
    | (have j1 := eq530 y x
       grind)
    | exact resolve eq6869 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq6869
  have eq6884 : y = (M.op x x) := by
    first
    | (have r₁ := eq6879
       have r₂ := eq16
       grind)
    | exact resolve eq6879 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6879
  have eq6889 : (M.op x y) = (k y x) := by grind
  clear eq6884
  have eq6900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq445 x y
       have i₂ := eq6889
       grind)
    | exact superpose eq6889 eq445
    | (have j0 := eq445 x y
       grind)
    | exact resolve eq445 eq6889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq6901 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq6900
       have r₂ := eq16
       grind)
    | exact resolve eq6900 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900
  have eq6927 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq6901
  have eq6940 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq6927
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6927
    | exact resolve eq6927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6927
  have eq6950 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6940
       have i₂ := eq6889
       grind)
    | exact superpose eq6889 eq6940
    | exact resolve eq6940 eq6889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889 eq6940
  have eq6955 : False := by grind
  exact eq6955

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
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
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq100
  have eq151 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq153 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | exact resolve eq151 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq806 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156 x y
       grind)
    | exact superpose eq156 eq16
    | (have j1 := eq156 x y
       grind)
    | exact resolve eq16 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq885 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153
    | exact resolve eq153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq938 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq885
    | (have j0 := eq885 X0 X1
       grind)
    | exact resolve eq885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq4576 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq806
       have i₂ := eq938 y x
       grind)
    | exact superpose eq938 eq806
    | (have j1 := eq938 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq806
       have r₂ := eq938 y x
       grind)
    | (have r₁ := eq806
       have r₂ := eq938 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq806
       have r₂ := eq938 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq806 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq938
  have eq4577 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq4576
  have eq4579 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4577
       grind)
    | exact superpose eq4577 eq16
    | exact resolve eq16 eq4577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4577
  have eq4580 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4579
       have r₂ := eq80 x
       grind)
    | exact resolve eq4579 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4579
  have eq4585 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq4580
       grind)
    | exact superpose eq4580 eq103
    | exact resolve eq103 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4594 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4585
       have r₂ := eq16
       grind)
    | exact resolve eq4585 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4585
  have eq4597 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4594
       grind)
    | exact superpose eq4594 eq10
    | exact resolve eq10 eq4594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4594
  have eq4646 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4597
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4597
    | exact resolve eq4597 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597
  have eq4649 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4646
       grind)
    | exact superpose eq4646 eq16
    | exact resolve eq16 eq4646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4646
  have eq4650 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4649
       have r₂ := eq80 x
       grind)
    | exact resolve eq4649 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4649
  have eq4655 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq4650
       grind)
    | exact superpose eq4650 eq10
    | exact resolve eq10 eq4650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4650
  have eq4704 : y = (M.op x x) := by
    first
    | (have i₁ := eq4655
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4655
    | exact resolve eq4655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655
  have eq4714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq4704
       grind)
    | exact superpose eq4704 eq103
    | exact resolve eq103 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4704
  have eq4722 : False := by grind
  exact eq4722

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq22
  have eq270 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq273 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq273 (σ X0)
       grind)
    | exact superpose eq273 eq15
    | exact resolve eq15 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq273 (τ X0)
       grind)
    | exact superpose eq273 eq31
    | exact resolve eq31 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq297 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq290
    | exact resolve eq290 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq284 X0
       have i₂ := eq273 X0
       grind)
    | exact superpose eq273 eq284
    | exact resolve eq284 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq284
  have eq349 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq303 X0
       grind)
    | exact superpose eq303 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq351 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq349 X0 X1
       have j1 := eq350 X0 X1
       grind)
    | (have r₁ := eq349 X0 X1
       have r₂ := eq350 X0 X1
       grind)
    | exact resolve eq349 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq350
  have eq365 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq367 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq365 X0 X1
       have j1 := eq366 X0 X1
       grind)
    | (have r₁ := eq365 X0 X1
       have r₂ := eq366 X0 X1
       grind)
    | exact resolve eq365 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq366
  have eq370 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq351 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq351
    | exact resolve eq351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq351 y (σ x)
       grind)
    | exact superpose eq351 eq16
    | (have j1 := eq351 y (σ x)
       grind)
    | exact resolve eq16 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351
  have eq391 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq387
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq387
    | exact resolve eq387 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq402 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq370 X1 X0
       grind)
    | exact superpose eq370 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq370 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq370 X0 X1
       grind)
    | exact resolve eq13 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq415 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq420 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq415 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq415 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq415 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq434 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq420 X0 (τ X1)
       grind)
    | exact superpose eq420 eq18
    | (have j1 := eq420 X0 (τ X1)
       grind)
    | exact resolve eq18 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq451 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq420 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq434 (τ X0) X1
       grind)
    | exact superpose eq434 eq17
    | (have j1 := eq434 (τ X0) X1
       grind)
    | exact resolve eq17 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq434
  have eq753 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq746
    | (have j0 := eq746 X0 X1
       grind)
    | exact resolve eq746 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq764 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq753
    | (have j0 := eq753 X0 X1
       grind)
    | exact resolve eq753 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq765 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq764 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq764
    | (have j0 := eq764 X0 X1
       grind)
    | exact resolve eq764 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq819 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq765 X0 X1
       have i₂ := eq420 X0 X1
       grind)
    | exact superpose eq420 eq765
    | (have j0 := eq765 X0 X1
       have j1 := eq420 X0 X1
       grind)
    | exact resolve eq765 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq765
  have eq883 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq819 X0 X1
       have j1 := eq451 X0 X1
       grind)
    | (have r₁ := eq819 X0 X1
       have r₂ := eq451 X0 X1
       grind)
    | exact resolve eq819 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq819
  have eq936 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq883 (σ X0) X1
       grind)
    | exact superpose eq883 eq28
    | (have j1 := eq883 (σ X0) X1
       grind)
    | exact resolve eq28 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq883
  have eq954 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq936 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq936
    | (have j0 := eq936 X0 X1
       grind)
    | exact resolve eq936 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq980 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq954 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq954
    | (have j0 := eq954 X0 X1
       grind)
    | exact resolve eq954 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq1392 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq980 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq980
    | exact resolve eq980 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1407 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X1 X0
       have i₂ := eq980 X0 X1
       grind)
    | exact superpose eq980 eq367
    | (have j0 := eq367 X1 X0
       have j1 := eq980 X0 X1
       grind)
    | exact resolve eq367 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq980
  have eq1422 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1407 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1461 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1392 y x
       grind)
    | exact superpose eq1392 eq16
    | (have j1 := eq1392 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1392 y x
       grind)
    | exact resolve eq16 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1478 : x = (k x y) := by grind
  clear eq1461
  have eq1720 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1422
    | exact resolve eq1422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq1840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1720 y x
       grind)
    | exact superpose eq1720 eq16
    | (have j1 := eq1720 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1720 y x
       grind)
    | exact resolve eq16 eq1720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq1858 : x = (M.op x y) := by grind
  clear eq1840
  have eq2044 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq391
       have i₂ := eq1858
       grind)
    | exact superpose eq1858 eq391
    | exact resolve eq391 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq2049 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq2044
  have eq2052 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2049
       have i₂ := eq1478
       grind)
    | exact superpose eq1478 eq2049
    | exact resolve eq2049 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq2049
  have eq2057 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2052
       grind)
    | exact superpose eq2052 eq16
    | exact resolve eq16 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2077 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq2057
       have i₂ := eq1858
       grind)
    | exact superpose eq1858 eq2057
    | exact resolve eq2057 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq2057
  have eq2078 : False := by grind
  exact eq2078

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation3112 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3112 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq265 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq265 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq277 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq266 (σ X0)
       grind)
    | exact superpose eq266 eq15
    | exact resolve eq15 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq266 X0
       grind)
    | exact superpose eq266 eq277
    | exact resolve eq277 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq277
  have eq334 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq368 (σ X1) (σ X0)
       grind)
    | exact superpose eq368 eq15
    | (have j1 := eq368 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq383 X0 X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq383
    | (have j0 := eq383 X0 X1
       grind)
    | exact resolve eq383 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq649 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq368 X1 X0
       grind)
    | exact superpose eq368 eq400
    | (have j0 := eq400 X0 X1
       have j1 := eq368 X1 X0
       grind)
    | exact resolve eq400 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15613 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq649 X0 X1
       grind)
    | exact superpose eq649 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq649 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq649 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq649 X0 X1
       grind)
    | exact resolve eq13 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15616 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq15618 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq15613 X0 X1
       grind)
    | (have r₁ := eq15613 X0 X1
       have r₂ := eq296 X0
       grind)
    | exact resolve eq15613 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15613
  have eq15634 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15618 X0 X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq15618
    | (have j0 := eq15618 X0 X1
       grind)
    | exact resolve eq15618 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15618
  have eq15646 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15634 X0 X1
       have i₂ := eq296 X0
       grind)
    | exact superpose eq296 eq15634
    | (have j0 := eq15634 X0 X1
       grind)
    | exact resolve eq15634 eq296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq15634
  have eq15653 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15646 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq15646
    | (have j0 := eq15646 X0 X1
       grind)
    | exact resolve eq15646 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15646
  have eq15654 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | exact superpose eq368 eq15653
    | (have j0 := eq15653 X0 X1
       have j1 := eq368 X1 X0
       grind)
    | exact resolve eq15653 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq15653
  have eq15655 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq15654 X0 X1
       have j1 := eq15616 X0 X1
       grind)
    | (have r₁ := eq15654 X0 X1
       have r₂ := eq15616 X0 X1
       grind)
    | (have r₁ := eq15654 X1 X1
       have r₂ := eq15616 X1 X1
       grind)
    | exact resolve eq15654 eq15616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15616 eq15654
  have eq15720 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15655 x y
       grind)
    | exact superpose eq15655 eq16
    | (have j1 := eq15655 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq15655 x y
       grind)
    | exact resolve eq16 eq15655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15655
  have eq15731 : (σ x) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq15720
  have eq15775 : (M.op x x) = (τ (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq15731
       grind)
    | exact superpose eq15731 eq10
    | exact resolve eq10 eq15731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15731
  have eq15955 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq15775
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15775
    | exact resolve eq15775 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15775
  have eq15981 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15955
       grind)
    | exact superpose eq15955 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15955
       grind)
    | exact resolve eq13 eq15955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15984 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
  clear eq15981
  have eq15985 : (M.op x x) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq15984
  have eq15988 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq400 x y
       have i₂ := eq15985
       grind)
    | exact superpose eq15985 eq400
    | (have j0 := eq400 x y
       grind)
    | exact resolve eq400 eq15985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq15985
  have eq15999 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq15988
  have eq16018 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15999
       grind)
    | exact superpose eq15999 eq16
    | exact resolve eq16 eq15999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15999
  have eq16030 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15955 eq16018
    | exact resolve eq16018 eq15955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15955 eq16018
  have eq16031 : x = (M.op x x) := by grind
  clear eq16030
  have eq16036 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq16031
       grind)
    | exact superpose eq16031 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq16031
       grind)
    | exact resolve eq12 eq16031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16039 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq334 x X0
       have i₂ := eq16031
       grind)
    | exact superpose eq16031 eq334
    | (have j0 := eq334 x X0
       grind)
    | exact resolve eq334 eq16031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq16031
  have eq16069 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq16039 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16039
  have eq16070 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq16036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16036
  have eq16537 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq16069 (σ X0)
       grind)
    | exact superpose eq16069 eq15
    | exact resolve eq15 eq16069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16069
  have eq16658 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq16537 X0
       have i₂ := eq16070 X0
       grind)
    | exact superpose eq16070 eq16537
    | exact resolve eq16537 eq16070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16070 eq16537
  have eq17125 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16658 y
       grind)
    | exact superpose eq16658 eq16
    | (have r₁ := eq16
       have r₂ := eq16658 y
       grind)
    | exact resolve eq16 eq16658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16658
  have eq17193 : False := by grind
  exact eq17193

/-- `Equation3112`: `x = (((y ◇ x) ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3112 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3112 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3112.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq117 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq612 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq117 X1 X0
       grind)
    | exact superpose eq117 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq117 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq117 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X0)
       have r₂ := eq117 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq13 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq617 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq618 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq617 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq698 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2161 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq618
    | exact resolve eq618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq2203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2161 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2161
    | (have j0 := eq2161 X0 X1
       grind)
    | exact resolve eq2161 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2239 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2203 X0 X1
       grind)
    | exact superpose eq2203 eq10
    | (have j1 := eq2203 X0 X1
       grind)
    | exact resolve eq10 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2280 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2239 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2239
    | (have j0 := eq2239 X0 X1
       grind)
    | exact resolve eq2239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2318 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq2280 (σ X0) X1
       grind)
    | exact superpose eq2280 eq37
    | (have j1 := eq2280 (σ X0) X1
       grind)
    | exact resolve eq37 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2280
  have eq4034 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq2318 X1 (σ X0)
       grind)
    | exact superpose eq2318 eq28
    | (have j1 := eq2318 X1 (σ X0)
       grind)
    | exact resolve eq28 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2318
  have eq4095 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4034 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4034
    | (have j0 := eq4034 X0 X1
       grind)
    | exact resolve eq4034 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034
  have eq4129 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4095 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4095
    | (have j0 := eq4095 X0 X1
       grind)
    | exact resolve eq4095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4095
  have eq4139 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4129 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4129
    | (have j0 := eq4129 X0 X1
       grind)
    | exact resolve eq4129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq4343 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4139 X1 X0
       grind)
    | exact superpose eq4139 eq11
    | (have j1 := eq4139 X1 X0
       grind)
    | exact resolve eq11 eq4139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq5212 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4343 x y
       grind)
    | exact superpose eq4343 eq16
    | (have j1 := eq4343 x y
       grind)
    | exact resolve eq16 eq4343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4343
  have eq5239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq5212
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5212
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5212
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5212
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5212 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq5212
       have i₂ := eq2203 x y
       grind)
    | exact superpose eq2203 eq5212
    | (have j1 := eq2203 x y
       grind)
    | (have r₁ := eq5212
       have r₂ := eq2203 x y
       grind)
    | (have r₁ := eq5212
       have r₂ := eq2203 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5212
       have r₂ := eq2203 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5212 eq2203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203 eq5212
  have eq5243 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5240
  have eq5244 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5243
  have eq5245 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5239
  have eq5246 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5245
  have eq5250 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5244
       grind)
    | exact superpose eq5244 eq16
    | exact resolve eq16 eq5244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5244
  have eq5251 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5250
       have r₂ := eq22 x
       grind)
    | exact resolve eq5250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5256 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq698 x y
       have i₂ := eq5251
       grind)
    | exact superpose eq5251 eq698
    | (have j0 := eq698 x y
       grind)
    | exact resolve eq698 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq5251
  have eq5262 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5256
  have eq5263 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5262
  have eq5267 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5246
       grind)
    | exact superpose eq5246 eq16
    | exact resolve eq16 eq5246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5246
  have eq5268 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5267
       have r₂ := eq22 x
       grind)
    | exact resolve eq5267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5267
  have eq5279 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5263
       grind)
    | exact superpose eq5263 eq16
    | exact resolve eq16 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263
  have eq5300 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5279
       have i₂ := eq5268
       grind)
    | exact superpose eq5268 eq5279
    | exact resolve eq5279 eq5268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268 eq5279
  have eq5301 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq5300
  have eq5302 : (σ x) = (σ y) := by grind
  clear eq5301
  have eq5303 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5302
       grind)
    | exact superpose eq5302 eq16
    | exact resolve eq16 eq5302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5304 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5302
       grind)
    | exact superpose eq5302 eq10
    | exact resolve eq10 eq5302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302
  have eq5355 : x = y := by
    first
    | (have i₁ := eq5304
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5304
    | exact resolve eq5304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304
  have eq5356 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5303
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq5303
    | exact resolve eq5303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5303
  have eq5357 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5356
       have i₂ := eq5355
       grind)
    | exact superpose eq5355 eq5356
    | exact resolve eq5356 eq5355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5355 eq5356
  have eq5358 : False := by grind
  exact eq5358

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq48 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 X0
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq45
    | exact resolve eq45 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq77 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq102 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq26 X1 X2 X0
       grind)
    | exact superpose eq26 eq22
    | exact resolve eq22 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (k X0 (σ X1)) (σ X2)
       have i₂ := eq38 X0 X1 X2
       grind)
    | exact superpose eq38 eq14
    | (have j0 := eq14 (k X0 (σ X1)) (σ X2)
       grind)
    | exact resolve eq14 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq203 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) (σ X0)
       have i₂ := eq75 X1 X0
       grind)
    | exact superpose eq75 eq22
    | (have j1 := eq75 X1 X0
       grind)
    | exact resolve eq22 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45 (M.op X1 (τ X0)) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq45
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq45 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq599 X0 X1 X2
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq599
    | (have j0 := eq599 X0 X1 X2
       grind)
    | exact resolve eq599 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq599
  have eq758 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq49 x
       have i₂ := eq77 (τ x) x
       grind)
    | exact superpose eq77 eq49
    | (have j0 := eq49 X0
       have j1 := eq77 (τ X0) X0
       grind)
    | exact resolve eq49 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq768 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (M.op (τ X0) (τ X0)) X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq45
    | (have j1 := eq49 X0
       grind)
    | exact resolve eq45 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq49
  have eq780 : ∀ X0 : G, (k X0 (σ (τ X0))) = (k (k X0 (σ (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq758 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq790 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq768 X0
       have i₂ := eq10 (M.op (τ X0) (τ X0))
       grind)
    | exact superpose eq10 eq768
    | (have j0 := eq768 X0
       grind)
    | exact resolve eq768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq799 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq780 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq780
    | (have j0 := eq780 X0
       grind)
    | exact resolve eq780 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq812 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq790 X0
       have j1 := eq35 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq790 X0
       have r₂ := eq35 (τ X0) (τ X0)
       grind)
    | exact resolve eq790 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq1384 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 (k (σ X0) (σ X0)) X0
       have i₂ := eq799 (σ X0)
       grind)
    | exact superpose eq799 eq39
    | (have j1 := eq799 (σ X0)
       grind)
    | exact resolve eq39 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq1392 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k (k (τ (σ X0)) X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1384 x
       have i₂ := eq39 (σ x) x
       grind)
    | exact superpose eq39 eq1384
    | (have j0 := eq1384 X0
       grind)
    | exact resolve eq1384 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1409 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1392 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1392
    | (have j0 := eq1392 X0
       grind)
    | exact resolve eq1392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1423 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1409 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1409
    | (have j0 := eq1409 X0
       grind)
    | exact resolve eq1409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409
  have eq1684 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq203 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1685 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1879 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X0) X1
       have i₂ := eq1685 X0
       grind)
    | exact superpose eq1685 eq26
    | (have j1 := eq1685 X0
       grind)
    | exact resolve eq26 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1685
  have eq1918 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1879 X0 X1
       have i₂ := eq22 (σ X0) X1
       grind)
    | exact superpose eq22 eq1879
    | (have j0 := eq1879 X0 X1
       grind)
    | exact resolve eq1879 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq3578 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1918 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1918
    | (have j0 := eq1918 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq1918 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918
  have eq3637 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3578 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3578
    | (have j0 := eq3578 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq3578 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3578
  have eq3641 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3637 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3637
    | (have j0 := eq3637 (k X0 X0) X0
       grind)
    | exact resolve eq3637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3637
  have eq3658 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X0 X0) X0
       have i₂ := eq3641 X0 X1
       grind)
    | exact superpose eq3641 eq22
    | (have j1 := eq3641 X0 (k X0 X0)
       grind)
    | exact resolve eq22 eq3641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq3832 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3658 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3658
  have eq3833 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3832 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832
  have eq3847 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3833 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq3833
    | exact resolve eq3833 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3854 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22 X0 (k X0 X0)
       have i₂ := eq3833 X0
       grind)
    | exact superpose eq3833 eq22
    | exact resolve eq22 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3865 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 X0)) = (M.op X1 (M.op (M.op X0 X1) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 X0 (k X0 X0)
       have i₂ := eq3833 X0
       grind)
    | exact superpose eq3833 eq102
    | exact resolve eq102 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq3833
  have eq4121 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3854 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3854
    | exact resolve eq3854 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3854
  have eq4214 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (σ (k X0 X0)) (σ X0)
       have i₂ := eq4121 X0
       grind)
    | exact superpose eq4121 eq35
    | exact resolve eq35 eq4121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4243 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4214 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq4214
    | (have j0 := eq4214 X0
       grind)
    | exact resolve eq4214 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq26163 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1423 (τ X0)
       have i₂ := eq606 X0 (τ X0) X0
       grind)
    | exact superpose eq606 eq1423
    | (have j0 := eq1423 (τ X0)
       have j1 := eq606 X0 (τ X0) x
       grind)
    | exact resolve eq1423 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq1423
  have eq26190 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq26163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26163
  have eq26219 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq26190 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq26190
    | (have j0 := eq26190 X0
       grind)
    | exact resolve eq26190 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26190
  have eq26244 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26219 X0
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq26219
    | (have j0 := eq26219 X0
       grind)
    | exact resolve eq26219 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq26219
  have eq27131 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq26244 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26244
    | exact resolve eq26244 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27177 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0) (τ X0)
       have i₂ := eq26244 X0
       grind)
    | exact superpose eq26244 eq35
    | (have j1 := eq26244 X0
       grind)
    | (have r₁ := eq35 (τ X0) (τ X0)
       have r₂ := eq26244 X0
       grind)
    | exact resolve eq35 eq26244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq27248 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq26244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26244
  have eq27249 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq27177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27177
  have eq27274 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27249 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq27249
    | (have j0 := eq27249 X0
       grind)
    | exact resolve eq27249 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq27249
  have eq27296 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27131 X0
       have i₂ := eq39 (σ X0) X0
       grind)
    | exact superpose eq39 eq27131
    | (have j0 := eq27131 X0
       grind)
    | exact resolve eq27131 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq27131
  have eq27302 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq27274 X0
       have j1 := eq27248 X0
       grind)
    | (have r₁ := eq27274 X0
       have r₂ := eq27248 X0
       grind)
    | exact resolve eq27274 eq27248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27248 eq27274
  have eq27310 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27296 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27296
    | (have j0 := eq27296 X0
       grind)
    | exact resolve eq27296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27296
  have eq27313 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq27310 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq27310 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq27310 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27310
  have eq27695 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3847 X0
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq3847
    | exact resolve eq3847 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3847
  have eq27708 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4121 X0
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq4121
    | exact resolve eq4121 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4121
  have eq27717 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4243 X0
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq4243
    | exact resolve eq4243 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq27770 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq27313 (σ X0)
       grind)
    | exact superpose eq27313 eq15
    | exact resolve eq15 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27838 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27770 X0
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq27770
    | exact resolve eq27770 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27770
  have eq28871 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (k (σ X0) (σ X0))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (k (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq3865 (σ X0) (σ X0)
       have i₂ := eq27838 X0
       grind)
    | exact superpose eq27838 eq3865
    | exact resolve eq3865 eq27838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq28895 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (k X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq28871 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq28871
    | exact resolve eq28871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28871
  have eq28938 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq28895 X0
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq28895
    | exact resolve eq28895 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28895
  have eq28961 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq28938 X0
       have i₂ := eq27838 (M.op X0 X0)
       grind)
    | exact superpose eq27838 eq28938
    | exact resolve eq28938 eq27838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28938
  have eq29028 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 (M.op X0 X0) X0
       have i₂ := eq27708 X0
       grind)
    | exact superpose eq27708 eq75
    | (have j0 := eq75 (M.op X0 X0) X0
       grind)
    | exact resolve eq75 eq27708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq27708
  have eq29130 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq29028 X0
       have j1 := eq27717 X0
       grind)
    | (have r₁ := eq29028 X0
       have r₂ := eq27717 X0
       grind)
    | exact resolve eq29028 eq27717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29028
  have eq29166 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq29130 X0
       have i₂ := eq27838 (M.op X0 X0)
       grind)
    | exact superpose eq27838 eq29130
    | (have j0 := eq29130 X0
       grind)
    | exact resolve eq29130 eq27838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29130
  have eq258915 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq28961 X0
       have i₂ := eq29166 X0
       grind)
    | exact superpose eq29166 eq28961
    | (have j1 := eq29166 X0
       grind)
    | exact resolve eq28961 eq29166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28961 eq29166
  have eq259356 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq258915 X0
       have i₂ := eq27838 X0
       grind)
    | exact superpose eq27838 eq258915
    | (have j0 := eq258915 X0
       grind)
    | exact resolve eq258915 eq27838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258915
  have eq259409 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq259356 X0
       have j1 := eq27717 X0
       grind)
    | (have r₁ := eq259356 X0
       have r₂ := eq27717 X0
       grind)
    | exact resolve eq259356 eq27717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27717 eq259356
  have eq260627 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq259409 X0
       grind)
    | exact superpose eq259409 eq10
    | exact resolve eq10 eq259409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260628 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (M.op X0 X0)) X1
       have i₂ := eq259409 X0
       grind)
    | exact superpose eq259409 eq15
    | exact resolve eq15 eq259409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259409
  have eq261012 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq260628 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq260628
    | exact resolve eq260628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260628
  have eq261013 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq260627 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq260627
    | exact resolve eq260627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260627
  have eq261414 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 (M.op (τ X0) (τ X0)) X1
       have i₂ := eq261013 (τ X0)
       grind)
    | exact superpose eq261013 eq184
    | (have j0 := eq184 X0 (M.op (τ X0) (τ X0)) X1
       grind)
    | exact resolve eq184 eq261013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq261501 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k X0 (σ (τ (k X0 X0))))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261414 X0 X1
       have i₂ := eq27302 X0
       grind)
    | exact superpose eq27302 eq261414
    | (have j0 := eq261414 X0 X1
       grind)
    | exact resolve eq261414 eq27302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261414
  have eq261588 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k X0 (k X0 X0))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261501 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq261501
    | (have j0 := eq261501 X0 X1
       grind)
    | exact resolve eq261501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261501
  have eq261654 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k X0 (M.op X0 X0))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261588 X0 X1
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq261588
    | (have j0 := eq261588 X0 X1
       grind)
    | exact resolve eq261588 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261588
  have eq261705 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261654 X0 X1
       have i₂ := eq261013 X0
       grind)
    | exact superpose eq261013 eq261654
    | (have j0 := eq261654 X0 X1
       grind)
    | exact resolve eq261654 eq261013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261654
  have eq261733 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261705 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq261705
    | (have j0 := eq261705 X0 X1
       grind)
    | exact resolve eq261705 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq261705
  have eq261750 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (σ (τ (k X0 X0)))) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261733 X0 X1
       have i₂ := eq27302 X0
       grind)
    | exact superpose eq27302 eq261733
    | (have j0 := eq261733 X0 X1
       grind)
    | exact resolve eq261733 eq27302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261733
  have eq261758 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (k X0 X0)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261750 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq261750
    | (have j0 := eq261750 X0 X1
       grind)
    | exact resolve eq261750 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261750
  have eq261762 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (M.op X0 X0)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261758 X0 X1
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq261758
    | (have j0 := eq261758 X0 X1
       grind)
    | exact resolve eq261758 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261758
  have eq261764 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261762 X0 X1
       have i₂ := eq261013 X0
       grind)
    | exact superpose eq261013 eq261762
    | (have j0 := eq261762 X0 X1
       grind)
    | exact resolve eq261762 eq261013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261762
  have eq261766 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (k X0 (σ (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq261764 X0 X1
       have i₂ := eq27838 X1
       grind)
    | exact superpose eq27838 eq261764
    | (have j0 := eq261764 X0 X1
       grind)
    | exact resolve eq261764 eq27838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27838 eq261764
  have eq261768 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (k X0 (σ (τ (k X0 X0))))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261766 X0 X1
       have i₂ := eq27302 X0
       grind)
    | exact superpose eq27302 eq261766
    | (have j0 := eq261766 X0 X1
       grind)
    | exact resolve eq261766 eq27302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261766
  have eq261769 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (k X0 (k X0 X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261768 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq261768
    | (have j0 := eq261768 X0 X1
       grind)
    | exact resolve eq261768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261768
  have eq261770 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (k X0 (M.op X0 X0))) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261769 X0 X1
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq261769
    | (have j0 := eq261769 X0 X1
       grind)
    | exact resolve eq261769 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261769
  have eq261771 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261770 X0 X1
       have i₂ := eq261013 X0
       grind)
    | exact superpose eq261013 eq261770
    | (have j0 := eq261770 X0 X1
       grind)
    | exact resolve eq261770 eq261013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261770
  have eq261772 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq261771 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq261771 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq261771 (M.op (σ (M.op X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq261771 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261771
  have eq270118 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261772 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq261772
    | (have j0 := eq261772 X1 (τ X0)
       grind)
    | exact resolve eq261772 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270469 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq261772 (σ X1) X0
       grind)
    | exact superpose eq261772 eq15
    | (have j1 := eq261772 (σ X1) X0
       grind)
    | exact resolve eq15 eq261772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261772
  have eq270736 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq270118 X0 X1
       have i₂ := eq27302 X0
       grind)
    | exact superpose eq27302 eq270118
    | (have j0 := eq270118 X0 X1
       grind)
    | exact resolve eq270118 eq27302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27302 eq270118
  have eq270842 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq270736 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq270736
    | (have j0 := eq270736 X0 X1
       grind)
    | exact resolve eq270736 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270736
  have eq270884 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270842 X0 X1
       have i₂ := eq27313 X0
       grind)
    | exact superpose eq27313 eq270842
    | (have j0 := eq270842 X0 X1
       grind)
    | exact resolve eq270842 eq27313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27313 eq270842
  have eq272435 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 (k X1 (M.op X1 X1)))) ∨ (M.op X0 X0) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq261012 X1 X0
       have i₂ := eq270884 X0 (k X1 (M.op X1 X1))
       grind)
    | exact superpose eq270884 eq261012
    | (have j1 := eq270884 X0 (k X1 (M.op X1 X1))
       grind)
    | exact resolve eq261012 eq270884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261012 eq270884
  have eq272590 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272435 X0 X1
       have i₂ := eq261013 X1
       grind)
    | exact superpose eq261013 eq272435
    | (have j0 := eq272435 X0 X1
       grind)
    | exact resolve eq272435 eq261013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272435
  have eq272771 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq272590 X0 X1
       have i₂ := eq261013 X1
       grind)
    | exact superpose eq261013 eq272590
    | (have j0 := eq272590 X0 X1
       grind)
    | exact resolve eq272590 eq261013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261013 eq272590
  have eq291025 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270469 x y
       grind)
    | exact superpose eq270469 eq16
    | (have j1 := eq270469 x y
       grind)
    | exact resolve eq16 eq270469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270469
  have eq292164 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq291025
       have i₂ := eq272771 x y
       grind)
    | exact superpose eq272771 eq291025
    | (have j1 := eq272771 x y
       grind)
    | (have r₁ := eq291025
       have r₂ := eq272771 x y
       grind)
    | exact resolve eq291025 eq272771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272771 eq291025
  have eq292171 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq292164
  have eq293889 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq292171
       grind)
    | exact superpose eq292171 eq10
    | exact resolve eq10 eq292171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292171
  have eq294294 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq293889
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq293889
    | exact resolve eq293889 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293889
  have eq294295 : y = (M.op x x) := by grind
  clear eq294294
  have eq294358 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27695 x
       have i₂ := eq294295
       grind)
    | exact superpose eq294295 eq27695
    | exact resolve eq27695 eq294295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27695
  have eq294453 : y = (M.op x y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq294295
       grind)
    | exact superpose eq294295 eq24
    | exact resolve eq24 eq294295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq294295
  have eq299333 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq294358
       grind)
    | exact superpose eq294358 eq16
    | exact resolve eq16 eq294358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294358
  have eq299600 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq299333
       have i₂ := eq294453
       grind)
    | exact superpose eq294453 eq299333
    | exact resolve eq299333 eq294453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294453 eq299333
  have eq299601 : False := by grind
  exact eq299601
