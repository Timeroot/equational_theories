import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_x_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq180 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (M.op (M.op (k (M.op X0 X0) X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq180 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq600 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq606 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq600
       grind)
    | exact superpose eq600 eq40
    | exact resolve eq40 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq607 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq606
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq606
    | exact resolve eq606 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq609 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq607
    | exact resolve eq607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq609 eq602
    | exact resolve eq602 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602 eq609
  have eq626 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq619
       have r₂ := eq27
       grind)
    | exact resolve eq619 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq633 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq626 eq180
    | exact resolve eq180 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq626 eq633
    | exact resolve eq633 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq633
  have eq640 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq635 eq142
    | exact resolve eq142 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq635
  have eq643 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq640
    | exact resolve eq640 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq640
  have eq646 : x = (M.op x x) := by
    first
    | (have j1 := eq604 x
       grind)
    | (have r₁ := eq643
       have r₂ := eq604 x
       grind)
    | exact resolve eq643 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq650 : ∀ X0 : G, (M.op (M.op (M.op x x) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq16
    | exact resolve eq16 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : (k x x) = (M.op x x) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq180
    | exact resolve eq180 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq654 : x = (k x x) := by
    first
    | (have i₁ := eq652
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq652
    | exact resolve eq652 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq655 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq650 X0
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq650
    | exact resolve eq650 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq656 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq655 X0
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq655
    | exact resolve eq655 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq655
  have eq658 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq654
       grind)
    | exact superpose eq654 eq40
    | exact resolve eq40 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq654
  have eq661 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq658
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq658
    | exact resolve eq658 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq658
  have eq666 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq656 y
       grind)
    | exact superpose eq656 eq18
    | (have j1 := eq656 y
       grind)
    | exact resolve eq18 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq656
  have eq678 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq666
       grind)
    | exact superpose eq666 eq24
    | exact resolve eq24 eq666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq666
  have eq684 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq678 eq20
    | exact resolve eq20 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq678
  have eq807 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq661 eq604
    | (have j0 := eq604 (σ x)
       grind)
    | (have r₁ := eq604 (σ x)
       have r₂ := eq661
       grind)
    | exact resolve eq604 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq808 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq807
  have eq816 : ∀ X0 : G, (M.op (M.op (k (σ x) (σ x)) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq808 eq547
    | exact resolve eq547 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq821 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq661 eq816
    | exact resolve eq816 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq816
  have eq824 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq808 eq821
    | exact resolve eq821 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq821
  have eq830 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq824 eq26
    | (have j1 := eq824 (σ y)
       grind)
    | exact resolve eq26 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq824
  have eq846 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq830 eq27
    | exact resolve eq27 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq830
  have eq847 : False := by grind
  exact eq847

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq20
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq49 (σ X0)
       grind)
    | exact superpose eq49 eq32
    | exact resolve eq32 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq87 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq49 (τ X0)
       grind)
    | exact superpose eq49 eq19
    | exact resolve eq19 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq90 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq88
    | exact resolve eq88 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq90
    | exact resolve eq90 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq90
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq96 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq96
    | exact resolve eq96 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq10
    | exact resolve eq10 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq171 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 y x
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq543 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq108 X0
       grind)
    | exact superpose eq108 eq36
    | exact resolve eq36 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq108
  have eq544 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq543
    | exact resolve eq543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq545 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq544
  have eq546 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq545 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq545
    | exact resolve eq545 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq587 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq546 X0
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq546
    | exact resolve eq546 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq546
  have eq591 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq587 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq587
    | exact resolve eq587 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq786 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq171
       have i₂ := eq100 x
       grind)
    | exact superpose eq100 eq171
    | exact resolve eq171 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq861 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq786
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq786
    | (have j1 := eq14 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq786
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq786
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq786 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq862 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq861
  have eq7825 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq862
       grind)
    | exact superpose eq862 eq16
    | exact resolve eq16 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq7826 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7825
       have r₂ := eq100 x
       grind)
    | exact resolve eq7825 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7825
  have eq182372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq591 x
       have i₂ := eq7826
       grind)
    | exact superpose eq7826 eq591
    | exact resolve eq591 eq7826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7826
  have eq182487 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq182372
       have r₂ := eq16
       grind)
    | exact resolve eq182372 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182372
  have eq182496 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq182487
       grind)
    | exact superpose eq182487 eq10
    | exact resolve eq10 eq182487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182487
  have eq182824 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq182496
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq182496
    | exact resolve eq182496 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182496
  have eq182826 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182824
       grind)
    | exact superpose eq182824 eq16
    | exact resolve eq16 eq182824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182824
  have eq182827 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq182826
       have r₂ := eq100 x
       grind)
    | exact resolve eq182826 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq182826
  have eq182879 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq182827
       grind)
    | exact superpose eq182827 eq10
    | exact resolve eq10 eq182827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182827
  have eq183297 : y = (M.op x x) := by
    first
    | (have i₁ := eq182879
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq182879
    | exact resolve eq182879 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182879
  have eq183505 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq591 x
       have i₂ := eq183297
       grind)
    | exact superpose eq183297 eq591
    | exact resolve eq591 eq183297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq183297
  have eq183619 : False := by grind
  exact eq183619

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq36 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq49 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq56 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq127 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq590 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq591 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq590 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq596 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq591 X0 X1
       have j1 := eq127 X0 X1
       grind)
    | (have r₁ := eq591 X0 X1
       have r₂ := eq127 X0 X1
       grind)
    | (have r₁ := eq591 X1 X1
       have r₂ := eq127 X1 X1
       grind)
    | exact resolve eq591 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq591
  have eq832 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq596 (σ X1) (σ X0)
       grind)
    | exact superpose eq596 eq15
    | exact resolve eq15 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1
       have i₂ := eq596 X1 X0
       grind)
    | exact superpose eq596 eq832
    | exact resolve eq832 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq832
  have eq843 : False := by grind
  exact eq843

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op y (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op y (M.op x y)) x)) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op y (M.op x y)) x)) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq644 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq180 eq181
    | exact resolve eq181 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq181
  have eq694 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq644 X0 (M.op X0 X0)
       grind)
    | exact superpose eq644 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq644 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq694 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq705 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X1)) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq695 X2 X0
       have i₂ := eq695 X1 X0
       grind)
    | exact superpose eq695 eq695
    | exact resolve eq695 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq644 X0 (M.op X0 X0)
       have i₂ := eq695 X1 (M.op X0 X0)
       grind)
    | exact superpose eq695 eq644
    | exact resolve eq644 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq741 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X0 (M.op X1 X1)
       have i₂ := eq695 X1 (τ X0)
       grind)
    | exact superpose eq695 eq34
    | exact resolve eq34 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (σ (M.op x x)) = (k (σ x) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op X0 X0)
       have i₂ := eq695 X0 x
       grind)
    | exact superpose eq695 eq35
    | exact resolve eq35 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq743 : ∀ X0 : G, (σ (M.op y y)) = (k (σ y) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq695 X0 y
       grind)
    | exact superpose eq695 eq36
    | exact resolve eq36 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq744 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq695 X0 sF0
       grind)
    | exact superpose eq695 eq37
    | exact resolve eq37 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq943 : ∀ X0 X1 X2 : G, (σ (k (τ X0) (M.op X1 X1))) = (k X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op X2 X2)
       have i₂ := eq705 (τ X0) X2 X1
       grind)
    | (have i₁ := eq34 X0 (M.op X2 X2)
       have i₂ := eq705 (τ X0) X1 X2
       grind)
    | exact superpose eq705 eq34
    | exact resolve eq34 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq956 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 X1))) = (k X0 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq943 X0 X1 X2
       have i₂ := eq34 X0 (M.op X1 X1)
       grind)
    | exact superpose eq34 eq943
    | exact resolve eq943 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq943
  have eq1176 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq1220 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq1225 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1245 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1176 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1260 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1245 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1245 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1245 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq4611 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1215
       grind)
    | exact superpose eq1215 eq39
    | exact resolve eq39 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq4612 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4611
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4611
    | exact resolve eq4611 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq4614 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4612
    | exact resolve eq4612 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4612
  have eq10689 : ∀ X0 X1 : G, (σ (k X0 (M.op X1 X1))) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 (M.op X1 X1)
       have i₂ := eq741 (σ X0) X1
       grind)
    | exact superpose eq741 eq10
    | exact resolve eq10 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq10776 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10689 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10689
    | exact resolve eq10689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10689
  have eq12550 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (k (σ (M.op X0 X0)) (σ (M.op X1 X1))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1260 (σ (M.op X0 X0)) X2
       have i₂ := eq956 (σ (M.op X0 X0)) X0 X1
       grind)
    | (have i₁ := eq1260 (σ (M.op X0 X0)) X2
       have i₂ := eq956 (σ (M.op X0 X0)) X1 X0
       grind)
    | exact superpose eq956 eq1260
    | (have j0 := eq1260 (σ (M.op X0 X0)) X2
       grind)
    | exact resolve eq1260 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq12657 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (k (M.op X0 X0) (M.op X1 X1))) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12550 X0 X1 X2
       have i₂ := eq10 (M.op X0 X0) (M.op X1 X1)
       grind)
    | exact superpose eq10 eq12550
    | (have j0 := eq12550 X0 X1 X2
       grind)
    | exact resolve eq12550 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550
  have eq12772 : ∀ X0 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq12657 X0 x X2
       have i₂ := eq738 X0 x
       grind)
    | exact superpose eq738 eq12657
    | (have j0 := eq12657 X0 x X2
       grind)
    | exact resolve eq12657 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12657
  have eq12773 : ∀ X0 X2 : G, (M.op X2 X2) = (k X2 (σ (M.op X0 X0))) := by
    intro X0 X2
    first
    | (have j0 := eq12772 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12772
  have eq12914 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq644 X0 X2
       have i₂ := eq12773 X1 X0
       grind)
    | exact superpose eq12773 eq644
    | exact resolve eq644 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13016 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq744 x
       have i₂ := eq12773 x sF1
       grind)
    | exact superpose eq12773 eq744
    | exact resolve eq744 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq13017 : ∀ X0 : G, (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 X0)
       have i₂ := eq12773 X0 sF1
       grind)
    | exact superpose eq12773 eq50
    | exact resolve eq50 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq13025 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq742 x
       have i₂ := eq12773 x sF2
       grind)
    | exact superpose eq12773 eq742
    | exact resolve eq742 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq13026 : ∀ X0 : G, (τ (M.op (σ x) (σ x))) = (k x (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (M.op X0 X0)
       have i₂ := eq12773 X0 sF2
       grind)
    | exact superpose eq12773 eq44
    | exact resolve eq44 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq13034 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq743 x
       have i₂ := eq12773 x sF3
       grind)
    | exact superpose eq12773 eq743
    | exact resolve eq743 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq13035 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) = (k y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op X0 X0)
       have i₂ := eq12773 X0 sF3
       grind)
    | exact superpose eq12773 eq47
    | exact resolve eq47 eq12773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq12773
  have eq13053 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq13035 x
       have i₂ := eq695 x y
       grind)
    | exact superpose eq695 eq13035
    | exact resolve eq13035 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13035
  have eq13061 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq13026 x
       have i₂ := eq695 x x
       grind)
    | exact superpose eq695 eq13026
    | exact resolve eq13026 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026
  have eq13069 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq13017 x
       have i₂ := eq695 x sF0
       grind)
    | exact superpose eq695 eq13017
    | exact resolve eq13017 eq695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13017
  have eq13169 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13016
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq13016
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13016 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13016
  have eq13225 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13169
  have eq13271 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq41 eq13225
    | exact resolve eq13225 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq13225
  have eq13309 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq13271
    | exact resolve eq13271 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13271
  have eq13328 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13025
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq13025
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq13025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13384 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13328
  have eq13430 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13384
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq13384
    | exact resolve eq13384 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13384
  have eq13468 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13430
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13430
    | exact resolve eq13430 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13430
  have eq13487 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13034
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq13034
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq13034 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13543 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq13487
  have eq13590 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13543
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq13543
    | exact resolve eq13543 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13543
  have eq13628 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13590
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13590
    | exact resolve eq13590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13590
  have eq13961 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 (M.op X1 X1))) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12914 (σ X0) X1 X2
       have i₂ := eq10 X0 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq12914
    | exact resolve eq12914 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12914
  have eq14667 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq13961 X0 x X2
       have i₂ := eq10776 X0 x
       grind)
    | exact superpose eq10776 eq13961
    | exact resolve eq13961 eq10776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10776 eq13961
  have eq30485 : (τ (k (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13309 eq13069
    | exact resolve eq13069 eq13309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13069 eq13309
  have eq30601 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq133 eq30485
    | exact resolve eq30485 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq30485
  have eq30607 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq30601
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq30601 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30601
  have eq30624 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30607 eq695
    | exact resolve eq695 eq30607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30630 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq30607 eq738
    | exact resolve eq738 eq30607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq30607
  have eq55457 : (τ (k (σ x) (σ x))) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq13468 eq13061
    | exact resolve eq13061 eq13468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13061 eq13468
  have eq55591 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq97 eq55457
    | exact resolve eq55457 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq55457
  have eq55605 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq55591
       have r₂ := eq13 x x
       grind)
    | exact resolve eq55591 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55591
  have eq55608 : (σ (k x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13025
       have i₂ := eq55605
       grind)
    | exact superpose eq55605 eq13025
    | exact resolve eq13025 eq55605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13025
  have eq55614 : ∀ X0 : G, (M.op (k x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq644 x X0
       have i₂ := eq55605
       grind)
    | exact superpose eq55605 eq644
    | exact resolve eq644 eq55605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq55746 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq55608
       have i₂ := eq39 x
       grind)
    | exact superpose eq39 eq55608
    | exact resolve eq55608 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq55608
  have eq55770 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq55746
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq55746
    | exact resolve eq55746 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55746
  have eq78453 : (τ (k (σ y) (σ y))) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq13628 eq13053
    | exact resolve eq13053 eq13628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13053 eq13628
  have eq78591 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq115 eq78453
    | exact resolve eq78453 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78453
  have eq78605 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq78591
       have r₂ := eq13 x y
       grind)
    | exact resolve eq78591 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78591
  have eq78608 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13034
       have i₂ := eq78605
       grind)
    | exact superpose eq78605 eq13034
    | exact resolve eq13034 eq78605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13034
  have eq78618 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k y y)) := by
    intro X0
    first
    | (have i₁ := eq695 y X0
       have i₂ := eq78605
       grind)
    | exact superpose eq78605 eq695
    | exact resolve eq695 eq78605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq78681 : (k y y) = (k (k y y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq30630 y
       have i₂ := eq78605
       grind)
    | exact superpose eq78605 eq30630
    | exact resolve eq30630 eq78605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30630
  have eq78750 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78608
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq78608
    | exact resolve eq78608 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq78608
  have eq78774 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq78750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq78750
    | exact resolve eq78750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78750
  have eq395207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4614 eq1220
    | exact resolve eq1220 eq4614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq4614
  have eq395216 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq395207
       have r₂ := eq27
       grind)
    | exact resolve eq395207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395207
  have eq395223 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq78774 eq395216
    | exact resolve eq395216 eq78774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78774 eq395216
  have eq395228 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq55770 eq395223
    | exact resolve eq395223 eq55770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55770 eq395223
  have eq395233 : x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq395228
       have i₂ := eq78605
       grind)
    | exact superpose eq78605 eq395228
    | exact resolve eq395228 eq78605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78605 eq395228
  have eq395235 : (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq395233
       have i₂ := eq55605
       grind)
    | exact superpose eq55605 eq395233
    | exact resolve eq395233 eq55605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55605 eq395233
  have eq400405 : (τ (σ x)) = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq395235 eq115
    | exact resolve eq115 eq395235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq395235
  have eq400467 : x = (k y y) ∨ x = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq400405
    | exact resolve eq400405 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400405
  have eq400468 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y y) ∨ x = (k x x) := by grind
  clear eq400467
  have eq400518 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq400468 eq141
    | exact resolve eq141 eq400468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq400468
  have eq400541 : x = (k x x) ∨ x = (k y y) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq400518
    | exact resolve eq400518 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq400518
  have eq400542 : x = (k y y) ∨ x = (k x x) := by grind
  clear eq400541
  have eq400565 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq78618 X0
       have i₂ := eq400542
       grind)
    | exact superpose eq400542 eq78618
    | exact resolve eq78618 eq400542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78618
  have eq400576 : x = (k x (k (M.op x y) (M.op x y))) ∨ x = (k x x) := by
    first
    | (have i₁ := eq78681
       have i₂ := eq400542
       grind)
    | exact superpose eq400542 eq78681
    | exact resolve eq78681 eq400542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78681 eq400542
  have eq400609 : x = (M.op x x) ∨ x = (k x x) := by
    first
    | exact superpose eq30624 eq400576
    | exact resolve eq400576 eq30624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30624 eq400576
  have eq400610 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq400565 X0
       have j1 := eq1260 x X0
       grind)
    | (have r₁ := eq400565 X0
       have r₂ := eq1260 x x
       grind)
    | exact resolve eq400565 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq400565
  have eq400620 : x = (M.op x x) := by
    first
    | (have j1 := eq1226 x
       grind)
    | (have r₁ := eq400609
       have r₂ := eq1226 x
       grind)
    | exact resolve eq400609 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq400609
  have eq400626 : x = (k x x) := by
    first
    | (have i₁ := eq400620
       have i₂ := eq400610 x
       grind)
    | exact superpose eq400610 eq400620
    | exact resolve eq400620 eq400610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400610 eq400620
  have eq400631 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55614 X0
       have i₂ := eq400626
       grind)
    | exact superpose eq400626 eq55614
    | exact resolve eq55614 eq400626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55614 eq400626
  have eq400705 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq400631 y
       grind)
    | exact superpose eq400631 eq18
    | (have j1 := eq400631 y
       grind)
    | exact resolve eq18 eq400631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq400790 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14667 x X0
       have i₂ := eq400631 x
       grind)
    | exact superpose eq400631 eq14667
    | exact resolve eq14667 eq400631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14667 eq400631
  have eq401062 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq400790 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq400790
    | (have j0 := eq400790 X0
       grind)
    | exact resolve eq400790 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq400790
  have eq401312 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq400705
       grind)
    | exact superpose eq400705 eq24
    | exact resolve eq24 eq400705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq400705
  have eq401495 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq401312 eq20
    | exact resolve eq20 eq401312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq401312
  have eq402310 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq401062 eq26
    | (have j1 := eq401062 (σ y)
       grind)
    | exact resolve eq26 eq401062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq401062
  have eq402991 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq402310 eq27
    | exact resolve eq27 eq402310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq402310
  have eq403060 : False := by grind
  exact eq403060

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq9 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X1) X2) = (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq66 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq66 X1 X2 (σ X0)
       grind)
    | exact superpose eq66 eq29
    | exact resolve eq29 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq70 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq66 X1 X2 (τ X0)
       grind)
    | exact superpose eq66 eq18
    | exact resolve eq18 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq71 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq69
    | exact resolve eq69 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq140 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq62 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq177 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 x (M.op X0 X0) X1
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq66
    | exact resolve eq66 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq178 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 x (M.op X0 X0)
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq71
    | exact resolve eq71 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq179 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 X1 x (M.op X0 X0)
       have i₂ := eq140 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq140 eq72
    | exact resolve eq72 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq140
  have eq267 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq267
    | (have j0 := eq267 (σ X0) (σ X1)
       grind)
    | exact resolve eq267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 (σ (M.op X1 X1))
       have i₂ := eq178 X1 X0
       grind)
    | exact superpose eq178 eq267
    | (have j0 := eq267 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq267 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1035 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq378 X1 X0
       have i₂ := eq267 X1 X0
       grind)
    | exact superpose eq267 eq378
    | (have j0 := eq378 X1 X0
       have j1 := eq267 (σ X1) (σ X0)
       grind)
    | exact resolve eq378 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq11276 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ (M.op X0 X0))
       have i₂ := eq384 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq384 eq12
    | (have j0 := eq12 X1 (σ (M.op X0 X0))
       have j1 := eq384 (σ (M.op X0 X0)) X0
       grind)
    | (have r₁ := eq12 X0 (σ (M.op X1 X1))
       have r₂ := eq384 (σ (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq11357 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq11276 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11276
  have eq11411 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq11357 X0 X1
       have j1 := eq12 X1 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq11357 X0 X1
       have r₂ := eq12 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq11357 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11357
  have eq11431 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11411 X0 X1
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq11411
    | exact resolve eq11411 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq11411
  have eq18677 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1035 x y
       grind)
    | exact superpose eq1035 eq16
    | (have j1 := eq1035 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1035 x y
       grind)
    | exact resolve eq16 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq18789 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq18677
  have eq18841 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq179 (σ y) X0
       have i₂ := eq18789
       grind)
    | exact superpose eq18789 eq179
    | exact resolve eq179 eq18789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq18789
  have eq18919 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq18841 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18841
    | exact resolve eq18841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18841
  have eq18926 : ∀ X0 X1 : G, (k X1 x) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 y X1
       have i₂ := eq18919 X0
       grind)
    | exact superpose eq18919 eq177
    | (have j1 := eq18919 X1
       grind)
    | exact resolve eq177 eq18919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq18919
  have eq19121 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq18926 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18926
  have eq19122 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq19121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19121
  have eq19164 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq19122 X0
       have i₂ := eq267 X0 x
       grind)
    | exact superpose eq267 eq19122
    | (have j1 := eq267 X0 x
       grind)
    | exact resolve eq19122 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq20431 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq19164 x
       grind)
    | exact superpose eq19164 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq19164 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq19164 x
       grind)
    | exact resolve eq12 eq19164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20570 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have j0 := eq19164 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19164
  have eq20571 : x = (M.op x x) := by grind
  clear eq20570
  have eq20573 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq20431 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20431
  have eq20683 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq20573 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq20573 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq20573 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20573
  have eq20704 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20683 X0
       have i₂ := eq19122 X0
       grind)
    | exact superpose eq19122 eq20683
    | exact resolve eq20683 eq19122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19122 eq20683
  have eq20736 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11431 x X0
       have i₂ := eq20571
       grind)
    | exact superpose eq20571 eq11431
    | exact resolve eq11431 eq20571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11431 eq20571
  have eq20973 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20704 y
       grind)
    | exact superpose eq20704 eq16
    | exact resolve eq16 eq20704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20704
  have eq21180 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq20973
       have i₂ := eq20736 (σ y)
       grind)
    | exact superpose eq20736 eq20973
    | (have r₁ := eq20973
       have r₂ := eq20736 (σ y)
       grind)
    | exact resolve eq20973 eq20736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20736 eq20973
  have eq21327 : False := by grind
  exact eq21327

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq14 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq89
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq89
    | exact resolve eq89 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq449 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq63 (M.op X0 X0) x x X3
       have i₂ := eq62 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq62 eq63
    | exact resolve eq63 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq63
  have eq479 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq449 X0 (M.op X0 X0)
       grind)
    | exact superpose eq449 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq449 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq550 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq75 X0 X0
       grind)
    | exact superpose eq75 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq75 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq75 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq13 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq557 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq556 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq559 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq550 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq565 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq559 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq559 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq559 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq1953 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq565 (τ X0) X1
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq565
    | (have j0 := eq565 (τ X0) X1
       grind)
    | exact resolve eq565 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq1985 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1953 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1953
    | (have j0 := eq1953 X0 X1
       grind)
    | exact resolve eq1953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1999 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1985 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1985
    | (have j0 := eq1985 X0 X1
       grind)
    | exact resolve eq1985 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1985
  have eq5056 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq557 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq557
    | (have j0 := eq557 (τ X0)
       grind)
    | exact resolve eq557 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq5091 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5056 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5056
    | (have j0 := eq5056 X0
       grind)
    | exact resolve eq5056 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5056
  have eq5106 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5091 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5091
    | (have j0 := eq5091 X0
       grind)
    | exact resolve eq5091 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq29317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq29318 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq29317
    | exact resolve eq29317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29317
  have eq29329 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq29318
       have r₂ := eq28
       grind)
    | exact resolve eq29318 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29318
  have eq29338 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29329 eq489
    | exact resolve eq489 eq29329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29329
  have eq29373 : ∀ X0 : G, x = (M.op y y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq29338 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq29338 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq29338 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq29338 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29338
  have eq29383 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq489 y X0
       have i₂ := eq29373 X1
       grind)
    | exact superpose eq29373 eq489
    | (have j1 := eq29373 X1
       grind)
    | exact resolve eq489 eq29373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq29373
  have eq29418 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29383 X0 X1
       have j1 := eq13 X1 (σ x)
       grind)
    | (have r₁ := eq29383 X0 X1
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq29383 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29383
  have eq29447 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq50
       have i₂ := eq29418 (k sF2 sF2) x
       grind)
    | exact superpose eq29418 eq50
    | (have j1 := eq29418 X0 x
       grind)
    | exact resolve eq50 eq29418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq29418
  have eq29562 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq29447
    | (have j0 := eq29447 x
       grind)
    | exact resolve eq29447 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29447
  have eq29599 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq29562 X0
       have j1 := eq1999 x X0
       grind)
    | (have r₁ := eq29562 X0
       have r₂ := eq1999 x x
       grind)
    | (have r₁ := eq29562 x
       have r₂ := eq1999 x x
       grind)
    | exact resolve eq29562 eq1999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1999 eq29562
  have eq29974 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq557 x
       have i₂ := eq29599 x
       grind)
    | exact superpose eq29599 eq557
    | (have j0 := eq557 x
       grind)
    | exact resolve eq557 eq29599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq29980 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5106 x
       have i₂ := eq29599 x
       grind)
    | exact superpose eq29599 eq5106
    | (have j0 := eq5106 x
       grind)
    | (have r₁ := eq5106 x
       have r₂ := eq29599 x
       grind)
    | exact resolve eq5106 eq29599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106 eq29599
  have eq30003 : x = (M.op x x) := by grind
  clear eq29980
  have eq30008 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq29974
  have eq30033 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq30008
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30008
    | exact resolve eq30008 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30008
  have eq30105 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq449 x X0
       have i₂ := eq30003
       grind)
    | exact superpose eq30003 eq449
    | exact resolve eq449 eq30003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30003
  have eq30729 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq30033 eq449
    | exact resolve eq449 eq30033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq30033
  have eq31384 : y = (M.op x y) := by
    first
    | (have i₁ := eq30105 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30105
    | (have j0 := eq30105 y
       grind)
    | exact resolve eq30105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30105
  have eq31522 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31384 eq21
    | exact resolve eq21 eq31384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31384
  have eq31691 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq31522
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31522
    | exact resolve eq31522 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31522
  have eq33626 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30729 eq27
    | (have j1 := eq30729 (σ y)
       grind)
    | exact resolve eq27 eq30729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30729
  have eq33756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31691 eq33626
    | exact resolve eq33626 eq31691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31691 eq33626
  have eq33765 : False := by grind
  exact eq33765

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pxy_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 (M.op X2 X1)) X2) X0
       have i₂ := eq16 (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq16 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq16 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq178 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq396 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq726 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
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
  have eq727 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq823 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq396 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq179 X1 X2 (σ X0)
       grind)
    | exact superpose eq179 eq396
    | exact resolve eq396 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq824 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq179 X1 X2 (τ X0)
       grind)
    | exact superpose eq179 eq34
    | exact resolve eq34 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq829 : ∀ X0 X1 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (M.op X1 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq179 X0 X1 sF2
       grind)
    | exact superpose eq179 eq90
    | exact resolve eq90 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq179
  have eq832 : ∀ X0 X1 : G, x = (k x (τ (M.op (M.op X0 (M.op X1 X0)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq29 eq829
    | exact resolve eq829 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829
  have eq837 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq824 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq824
    | exact resolve eq824 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq838 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (M.op X2 X1)) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq823 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq823
    | exact resolve eq823 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq1049 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq791 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq1341 : ∀ X0 X3 : G, (M.op (M.op X0 X0) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq177 (M.op X0 X0) x x X3
       have i₂ := eq176 X0 x x (M.op X0 X0)
       grind)
    | exact superpose eq176 eq177
    | exact resolve eq177 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq177
  have eq1412 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq837 X1 X0 (M.op X2 X2)
       have i₂ := eq1341 X2 X0
       grind)
    | exact superpose eq1341 eq837
    | exact resolve eq837 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq1413 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op (M.op X0 X0) (M.op X2 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq838 X1 X0 (M.op X2 X2)
       have i₂ := eq1341 X2 X0
       grind)
    | exact superpose eq1341 eq838
    | exact resolve eq838 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq1428 : ∀ X1 X2 : G, (k X1 (τ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1413 x X1 X2
       have i₂ := eq1341 x (M.op X2 X2)
       grind)
    | (have i₁ := eq1413 x X1 X2
       have i₂ := eq1341 x (M.op (M.op x x) (M.op X2 X2))
       grind)
    | exact superpose eq1341 eq1413
    | exact resolve eq1413 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1429 : ∀ X1 X2 : G, (k X1 (σ (M.op X2 X2))) = X1 := by
    intro X1 X2
    first
    | (have i₁ := eq1412 x X1 X2
       have i₂ := eq1341 x (M.op X2 X2)
       grind)
    | (have i₁ := eq1412 x X1 X2
       have i₂ := eq1341 x (M.op (M.op x x) (M.op X2 X2))
       grind)
    | exact superpose eq1341 eq1412
    | exact resolve eq1412 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1479 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1049 (σ (M.op X0 X0))
       have i₂ := eq1429 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq1429 eq1049
    | (have j0 := eq1049 (σ (M.op X0 X0))
       grind)
    | (have r₁ := eq1049 (σ (M.op x x))
       have r₂ := eq1429 (σ (M.op x x)) x
       grind)
    | exact resolve eq1049 eq1429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq1492 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1479 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1519 : ∀ X0 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1049 (τ (M.op X0 X0))
       have i₂ := eq1428 (τ (M.op X0 X0)) X0
       grind)
    | exact superpose eq1428 eq1049
    | (have j0 := eq1049 (τ (M.op X0 X0))
       grind)
    | (have r₁ := eq1049 (τ (M.op x x))
       have r₂ := eq1428 (τ (M.op x x)) x
       grind)
    | exact resolve eq1049 eq1428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1529 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq1519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq2285 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq726
       grind)
    | exact superpose eq726 eq39
    | exact resolve eq39 eq726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq2286 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2285
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2285
    | exact resolve eq2285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq2288 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2286
    | exact resolve eq2286 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq31874 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1341 (σ (M.op X0 X0)) X1
       have i₂ := eq1492 X0
       grind)
    | exact superpose eq1492 eq1341
    | exact resolve eq1341 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492
  have eq63799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2288 eq727
    | exact resolve eq727 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63808 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq63799
       have r₂ := eq27
       grind)
    | exact resolve eq63799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63799
  have eq63816 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq63808 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq63808
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq63808
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq63808
       grind)
    | exact resolve eq12 eq63808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63808
  have eq63850 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq63816
  have eq63854 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq63850
       have r₂ := eq26
       grind)
    | exact resolve eq63850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63850
  have eq63857 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2288 eq63854
    | exact resolve eq63854 eq2288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2288 eq63854
  have eq63858 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq63857
       have r₂ := eq27
       grind)
    | exact resolve eq63857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63857
  have eq63976 : x = (k x (τ (M.op (M.op (σ x) (σ x)) (σ x)))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq63858 eq832
    | exact resolve eq832 eq63858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq63858
  have eq64014 : x = (k x (τ (σ x))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63976
       have i₂ := eq1341 sF2 sF2
       grind)
    | (have i₁ := eq63976
       have i₂ := eq1341 x (M.op (M.op sF2 sF2) sF2)
       grind)
    | exact superpose eq1341 eq63976
    | exact resolve eq63976 eq1341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63976
  have eq64091 : x = (k x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq64014
    | exact resolve eq64014 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64014
  have eq64095 : (M.op x y) = (M.op y x) ∨ x = (k x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq64091
       have r₂ := eq13 x x
       grind)
    | exact resolve eq64091 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64091
  have eq64109 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq64095
       grind)
    | exact superpose eq64095 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq64095
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq64095
       grind)
    | exact resolve eq12 eq64095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64095
  have eq64145 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq1049 x
       grind)
    | (have r₁ := eq64109
       have r₂ := eq1049 x
       grind)
    | exact resolve eq64109 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq64109
  have eq64148 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq64145
       have r₂ := eq18
       grind)
    | exact resolve eq64145 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64145
  have eq64247 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq64148
       grind)
    | exact superpose eq64148 eq39
    | exact resolve eq39 eq64148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq64148
  have eq64250 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64247
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq64247
    | exact resolve eq64247 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64247
  have eq64254 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq64250
    | exact resolve eq64250 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64250
  have eq64259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq64254 eq727
    | exact resolve eq727 eq64254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq64268 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq64259
       have r₂ := eq27
       grind)
    | exact resolve eq64259 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64259
  have eq69267 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq64268 eq12
    | (have j0 := eq12 x (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq64268
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq64268
       grind)
    | exact resolve eq12 eq64268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64268
  have eq69301 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq69267
  have eq69305 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq69301
       have r₂ := eq26
       grind)
    | exact resolve eq69301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69301
  have eq69308 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq64254 eq69305
    | exact resolve eq69305 eq64254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64254 eq69305
  have eq69309 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq69308
       have r₂ := eq27
       grind)
    | exact resolve eq69308 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69308
  have eq69347 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq69309 eq1529
    | exact resolve eq1529 eq69309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq69309
  have eq69508 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq69347
    | exact resolve eq69347 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq69347
  have eq69509 : x = (M.op x x) := by grind
  clear eq69508
  have eq69572 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1341 x X0
       have i₂ := eq69509
       grind)
    | exact superpose eq69509 eq1341
    | exact resolve eq1341 eq69509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341
  have eq69624 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31874 x X0
       have i₂ := eq69509
       grind)
    | exact superpose eq69509 eq31874
    | exact resolve eq31874 eq69509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31874 eq69509
  have eq69725 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69624 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69624
    | (have j0 := eq69624 X0
       grind)
    | exact resolve eq69624 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq69624
  have eq69837 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq69572 y
       grind)
    | exact superpose eq69572 eq18
    | (have j1 := eq69572 y
       grind)
    | exact resolve eq18 eq69572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq69572
  have eq70241 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq69837
       grind)
    | exact superpose eq69837 eq24
    | exact resolve eq24 eq69837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq69837
  have eq70459 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq70241 eq20
    | exact resolve eq20 eq70241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq70241
  have eq71126 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69725 eq26
    | (have j1 := eq69725 (σ y)
       grind)
    | exact resolve eq26 eq69725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq69725
  have eq71506 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq71126 eq27
    | exact resolve eq27 eq71126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq71126
  have eq71619 : False := by grind
  exact eq71619

/-- `Equation2998`: `x = ((y ◇ (z ◇ y)) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_pyx_pxy_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2998 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2998.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq22 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq12 (τ X0) X1
       grind)
    | exact superpose eq12 eq17
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq17 eq12
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
  clear eq17
  have eq26 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | (have j0 := eq22 X0 X1
       grind)
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq49 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ X1)) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq12 (σ X0) X1
       grind)
    | exact superpose eq12 eq33
    | (have j1 := eq12 X0 X1
       grind)
    | exact resolve eq33 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op (M.op X1 (M.op X2 X1)) X2)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ X0) (τ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | (have j0 := eq26 X0 (τ X0)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq92 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq13 (σ X1) (σ X0)
       grind)
    | exact superpose eq13 eq15
    | (have j1 := eq13 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ X1))) ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (τ X1)
       have i₂ := eq57 (σ X0) X1
       grind)
    | exact superpose eq57 eq33
    | (have j1 := eq57 X0 X1
       grind)
    | exact resolve eq33 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k X0 (τ (τ X1))) = X0 ∨ (M.op X1 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq103
    | (have j0 := eq103 X0 X1
       grind)
    | exact resolve eq103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq240 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       have i₂ := eq71 X1 X0 (M.op X1 X1) (M.op X0 (M.op (M.op X1 X1) X0))
       grind)
    | exact superpose eq71 eq9
    | exact resolve eq9 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq252 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 x (M.op X0 X0)
       have i₂ := eq240 x X0 (M.op X0 X0)
       grind)
    | exact superpose eq240 eq9
    | exact resolve eq9 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq439 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92 x y
       grind)
    | exact superpose eq92 eq16
    | (have j1 := eq92 x y
       grind)
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq942 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208 x y
       grind)
    | exact superpose eq208 eq16
    | (have j1 := eq208 x y
       grind)
    | exact resolve eq16 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq954 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq208 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq955 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq954 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq966 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq955 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq955
    | exact resolve eq955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq252 (σ X0) X1
       have i₂ := eq955 X0
       grind)
    | exact superpose eq955 eq252
    | (have j1 := eq955 X0
       grind)
    | exact resolve eq252 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq987 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq966 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq966
    | (have j0 := eq966 X0
       grind)
    | exact resolve eq966 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq966
  have eq988 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq987 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq987
    | (have j0 := eq987 X0
       grind)
    | exact resolve eq987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1008 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 X0) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq988 (τ X0)
       grind)
    | exact superpose eq988 eq73
    | (have j0 := eq73 X0 X1
       have j1 := eq988 (τ X0)
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq988 (τ X0)
       grind)
    | (have r₁ := eq73 X0 X0
       have r₂ := eq988 X0
       grind)
    | exact resolve eq73 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq988
  have eq1009 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1008 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1019 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1009 X0 X1
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq1009
    | (have j0 := eq1009 X0 X1
       grind)
    | exact resolve eq1009 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1009
  have eq1084 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1019 X0 X1
       have i₂ := eq14 X0 X0
       grind)
    | exact superpose eq14 eq1019
    | (have j0 := eq1019 X0 X1
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq1019 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1112 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1084 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1120 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1112 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1112 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1112 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1302 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 (M.op X1 X0)) X1)) ≠ (τ (M.op (M.op X0 (M.op X1 X0)) X1)) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1120 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq1120
    | (have j0 := eq1120 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       grind)
    | exact resolve eq1120 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1306 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1120 (M.op X0 X0) X1
       have i₂ := eq252 X0 (M.op X0 X0)
       grind)
    | exact superpose eq252 eq1120
    | (have j0 := eq1120 (M.op X0 X0) X1
       grind)
    | exact resolve eq1120 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1316 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1320 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1302 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1344 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (M.op X1 X1)
       have i₂ := eq1316 X1 (σ X0)
       grind)
    | exact superpose eq1316 eq33
    | exact resolve eq33 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1354 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1344 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1344
    | exact resolve eq1344 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1495 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (τ (M.op X1 X1))
       have i₂ := eq1354 (σ X0) X1
       grind)
    | exact superpose eq1354 eq33
    | exact resolve eq33 eq1354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1354
  have eq1506 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1495 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1495
    | exact resolve eq1495 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq2796 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq979 X0 X1
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq979
    | (have j0 := eq979 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq979 X0 (σ X0)
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq979 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2799 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 (M.op X1 X0)) X1)) ≠ (σ (M.op (M.op X0 (M.op X1 X0)) X1)) ∨ (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq979 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq1320 X0 X1 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | exact superpose eq1320 eq979
    | (have j0 := eq979 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       grind)
    | exact resolve eq979 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq2814 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq979 (τ X0) X1
       have i₂ := eq57 (τ X0) X0
       grind)
    | exact superpose eq57 eq979
    | (have j0 := eq979 (τ X0) X1
       have j1 := eq57 X0 X0
       grind)
    | (have r₁ := eq979 X0 (σ X0)
       have r₂ := eq57 X0 (σ X0)
       grind)
    | exact resolve eq979 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq2816 : ∀ X0 X1 : G, (σ (τ (τ X0))) ≠ (σ (τ (τ X0))) ∨ (M.op (σ (τ (τ X0))) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq979 (τ (τ X0)) X1
       have i₂ := eq107 (τ (τ X0)) X0
       grind)
    | exact superpose eq107 eq979
    | (have j0 := eq979 (τ (τ X0)) X1
       have j1 := eq107 X0 X0
       grind)
    | (have r₁ := eq979 X0 (σ X0)
       have r₂ := eq107 X0 (σ X0)
       grind)
    | exact resolve eq979 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq2822 : ∀ X0 X1 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (M.op (σ (τ (τ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq979 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq1506 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq1506 eq979
    | (have j0 := eq979 (τ (τ (M.op X0 X0))) X1
       grind)
    | exact resolve eq979 eq1506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq1506
  have eq2837 : ∀ X0 X1 : G, (M.op (σ (τ (τ (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2822 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2822
  have eq2843 : ∀ X0 X1 : G, (M.op (σ (τ (τ X0))) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2816 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq2845 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2814 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814
  have eq2860 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2799 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq2863 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq2796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2796
  have eq2872 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2837 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq2837
    | exact resolve eq2837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2878 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2843 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq2843
    | (have j0 := eq2843 X0 X1
       grind)
    | exact resolve eq2843 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2843
  have eq2880 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2845 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2845
    | (have j0 := eq2845 X0 X1
       grind)
    | exact resolve eq2845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2984 : ∀ X0 X1 X2 : G, (M.op (τ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2872 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq9 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq9 eq2872
    | exact resolve eq2872 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq3358 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2880 (σ x) (σ y)
       grind)
    | exact superpose eq2880 eq16
    | (have j1 := eq2880 (σ x) x
       grind)
    | exact resolve eq16 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3819 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2878 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2878
    | (have j0 := eq2878 (σ X0) X1
       grind)
    | exact resolve eq2878 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878
  have eq7885 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x ≠ (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq439
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq439
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq439
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq439 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq7888 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x ≠ (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq7885
  have eq7891 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by
    first
    | (have j1 := eq2863 x (σ x)
       grind)
    | (have r₁ := eq7888
       have r₂ := eq2863 y (σ x)
       grind)
    | (have r₁ := eq7888
       have r₂ := eq2863 (σ x) x
       grind)
    | (have r₁ := eq7888
       have r₂ := eq2863 x x
       grind)
    | exact resolve eq7888 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq9210 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq942
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq942
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq942 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq9214 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq9210
  have eq9216 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq2863 y (σ y)
       grind)
    | (have r₁ := eq9214
       have r₂ := eq2863 (σ y) x
       grind)
    | (have r₁ := eq9214
       have r₂ := eq2863 y x
       grind)
    | exact resolve eq9214 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863 eq9214
  have eq87445 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by
    first
    | (have i₁ := eq3358
       have i₂ := eq7891
       grind)
    | exact superpose eq7891 eq3358
    | (have r₁ := eq3358
       have r₂ := eq7891
       grind)
    | exact resolve eq3358 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq87451 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op x X0) = X0 ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3819 x X0
       have i₂ := eq7891
       grind)
    | exact superpose eq7891 eq3819
    | (have j0 := eq3819 x X0
       grind)
    | (have r₁ := eq3819 x x
       have r₂ := eq7891
       grind)
    | (have r₁ := eq3819 (σ y) (σ x)
       have r₂ := eq7891
       grind)
    | (have r₁ := eq3819 y x
       have r₂ := eq7891
       grind)
    | exact resolve eq3819 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891
  have eq87599 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by
    intro X0
    first
    | (have j0 := eq87451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87451
  have eq87605 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by grind
  clear eq87445
  have eq87661 : (σ y) ≠ (σ y) ∨ (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by
    first
    | exact superpose eq87599 eq87605
    | exact resolve eq87605 eq87599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87599 eq87605
  have eq87662 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ x ≠ (M.op y x) := by grind
  clear eq87661
  have eq87679 : (σ x) ≠ (σ x) ∨ x ≠ (M.op y x) ∨ (σ y) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq87662
       have i₂ := eq2880 (σ y) (σ x)
       grind)
    | exact superpose eq2880 eq87662
    | (have j1 := eq2880 (σ y) x
       grind)
    | (have r₁ := eq87662
       have r₂ := eq2880 (σ y) (σ x)
       grind)
    | (have r₁ := eq87662
       have r₂ := eq2880 y x
       grind)
    | exact resolve eq87662 eq2880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880 eq87662
  have eq87682 : x ≠ (M.op y x) ∨ (σ y) ≠ (M.op (σ y) (σ y)) := by grind
  clear eq87679
  have eq87692 : (σ y) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq3819 y x
       grind)
    | (have r₁ := eq87682
       have r₂ := eq3819 y x
       grind)
    | (have r₁ := eq87682
       have r₂ := eq3819 (σ y) (σ y)
       grind)
    | exact resolve eq87682 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819 eq87682
  have eq87935 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87692
       have i₂ := eq9216
       grind)
    | exact superpose eq9216 eq87692
    | (have r₁ := eq87692
       have r₂ := eq9216
       grind)
    | exact resolve eq87692 eq9216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9216 eq87692
  have eq88095 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq87935
  have eq111657 : ∀ X0 : G, (M.op (τ (M.op (M.op (σ y) (σ y)) (σ x))) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2984 (σ y) (σ x) X0
       have i₂ := eq88095
       grind)
    | exact superpose eq88095 eq2984
    | exact resolve eq2984 eq88095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984 eq88095
  have eq111670 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq111657 X0
       have i₂ := eq252 (σ y) (σ x)
       grind)
    | (have i₁ := eq111657 X0
       have i₂ := eq252 X0 (M.op (M.op (σ y) (σ y)) (σ x))
       grind)
    | exact superpose eq252 eq111657
    | exact resolve eq111657 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111657
  have eq111692 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq111670 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq111670
    | exact resolve eq111670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111670
  have eq111772 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq111692 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111692
  have eq111773 : y = (M.op x y) := by grind
  clear eq111772
  have eq111774 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111773
       grind)
    | exact superpose eq111773 eq16
    | exact resolve eq16 eq111773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111832 : ∀ X0 : G, (M.op (σ (M.op (M.op y y) x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2860 y x X0
       have i₂ := eq111773
       grind)
    | exact superpose eq111773 eq2860
    | exact resolve eq2860 eq111773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860 eq111773
  have eq111847 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq111832 X0
       have i₂ := eq252 y x
       grind)
    | (have i₁ := eq111832 X0
       have i₂ := eq252 X0 (M.op (M.op y y) x)
       grind)
    | exact superpose eq252 eq111832
    | exact resolve eq111832 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq111832
  have eq111936 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq111774
       have i₂ := eq111847 (σ y)
       grind)
    | exact superpose eq111847 eq111774
    | (have r₁ := eq111774
       have r₂ := eq111847 (σ y)
       grind)
    | exact resolve eq111774 eq111847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111774 eq111847
  have eq111973 : False := by grind
  exact eq111973
