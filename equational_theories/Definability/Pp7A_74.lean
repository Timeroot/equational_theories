import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4079`: `x ◇ x = ((x ◇ y) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_x_pxy_y_pxy_Equation4079 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4079 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4079.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  clear eq24
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
  have eq179 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 (M.op (M.op X0 X1) X2) (M.op X0 X0)
       have r₂ := eq16 X0 X1 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) ∨ (M.op (M.op (M.op X0 X1) X2) X3) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (M.op x y) = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq586 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq598 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (k X0 X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq564 X0 X1 X2 X3
       have j1 := eq185 X0 X1 X2 X3
       grind)
    | (have r₁ := eq564 X0 X1 X2 X3
       have r₂ := eq185 X0 X1 X2 X3
       grind)
    | exact resolve eq564 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq564
  have eq600 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq580
       grind)
    | exact superpose eq580 eq41
    | exact resolve eq41 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq580
  have eq601 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq600
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq600
    | exact resolve eq600 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq603 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq601
    | exact resolve eq601 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq613 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq603 eq583
    | exact resolve eq583 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq603
  have eq620 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq613
       have r₂ := eq27
       grind)
    | exact resolve eq613 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq626 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq620 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq620
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq620
       grind)
    | exact resolve eq13 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq628 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq626
  have eq631 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq628 eq142
    | exact resolve eq142 eq628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq628
  have eq634 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq30 eq631
    | exact resolve eq631 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq631
  have eq637 : x = (M.op x x) := by
    first
    | (have j1 := eq586 x
       grind)
    | (have r₁ := eq634
       have r₂ := eq586 x
       grind)
    | exact resolve eq634 eq586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq642 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq637
       grind)
    | exact superpose eq637 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq637
       grind)
    | exact resolve eq13 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, x = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x x x x
       have i₂ := eq637
       grind)
    | exact superpose eq637 eq16
    | exact resolve eq16 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq644 : x = (k x x) := by grind
  clear eq642
  have eq646 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq644
       grind)
    | exact superpose eq644 eq40
    | exact resolve eq40 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq649 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq646
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq646
    | exact resolve eq646 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq654 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq649 eq586
    | (have j0 := eq586 (σ x)
       grind)
    | (have r₁ := eq586 (σ x)
       have r₂ := eq649
       grind)
    | exact resolve eq586 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586
  have eq655 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq654
  have eq662 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq655 eq16
    | exact resolve eq16 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq699 : ∀ X0 X1 : G, (k x x) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq598 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq598
    | (have j0 := eq598 x y X0 X1
       grind)
    | exact resolve eq598 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq598
    | (have j0 := eq598 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x x) X2) := by
    intro X2
    first
    | exact superpose eq179 eq598
    | exact resolve eq598 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq707 : ∀ X2 : G, (M.op (M.op (σ x) (σ x)) X2) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X2
    first
    | exact superpose eq180 eq598
    | exact resolve eq598 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq744 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq662 eq707
    | exact resolve eq707 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq707
  have eq745 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq706 x
       have i₂ := eq643 x x
       grind)
    | exact superpose eq643 eq706
    | exact resolve eq706 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq706
  have eq748 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq649 eq701
    | exact resolve eq701 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq701
  have eq750 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq699 X0 X1
       have i₂ := eq644
       grind)
    | exact superpose eq644 eq699
    | exact resolve eq699 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq699
  have eq797 : ∀ X2 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) X2) := by
    intro X2
    first
    | exact superpose eq748 eq598
    | exact resolve eq598 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq810 : ∀ X2 : G, (σ x) = (M.op (σ x) X2) := by
    intro X2
    first
    | exact superpose eq744 eq797
    | exact resolve eq797 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq797
  have eq820 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq810 eq26
    | (have j1 := eq810 (σ y)
       grind)
    | exact resolve eq26 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq810
  have eq834 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq820 eq27
    | exact resolve eq27 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq820
  have eq841 : ∀ X2 : G, (k (M.op x y) (M.op x y)) = (M.op x X2) := by
    intro X2
    first
    | exact superpose eq750 eq598
    | exact resolve eq598 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq750
  have eq854 : ∀ X2 : G, x = (M.op x X2) := by
    intro X2
    first
    | exact superpose eq745 eq841
    | exact resolve eq841 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq841
  have eq864 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq854 y
       grind)
    | exact superpose eq854 eq18
    | (have j1 := eq854 y
       grind)
    | exact resolve eq18 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq854
  have eq876 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq22
    | exact resolve eq22 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq864
  have eq886 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq876 eq20
    | exact resolve eq20 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq876
  have eq904 : False := by grind
  exact eq904

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_pyy_pxx_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X1 (M.op x x) x X4
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have r₁ := eq13 (M.op X1 X1) (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) ≠ X1 ∨ (k X1 X1) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq178 X0 X1
       grind)
    | (have i₁ := eq13 X1 (M.op (M.op x y) y)
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op x y) y) X1) (M.op (M.op (M.op x y) y) X1)
       have r₂ := eq178 (M.op (M.op (M.op x y) y) X1) X1
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ≠ X1 ∨ (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq179 X0 X1
       grind)
    | (have i₁ := eq13 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq13
    | (have r₁ := eq13 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1)
       have r₂ := eq179 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180 x X1 X3
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq180 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq180
    | exact resolve eq180 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq504 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq420 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq420
    | exact resolve eq420 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq1298 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq200 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1329 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) X0) = X1 ∨ (M.op (M.op (M.op x y) y) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq178 X0 X1
       grind)
    | (have i₁ := eq11 X1 (M.op (M.op x y) y)
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq11
    | exact resolve eq11 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1330 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq179 X0 X1
       grind)
    | (have i₁ := eq11 X1 (M.op (M.op (σ x) (σ y)) (σ y))
       have i₂ := eq179 X0 X1
       grind)
    | exact superpose eq179 eq11
    | exact resolve eq11 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1333 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1355 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq1356 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1411 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1412 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq1433 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1333 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1436 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1437 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1445 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1433 X0 X1
       have j1 := eq200 X0 X1
       grind)
    | (have r₁ := eq1433 X0 X1
       have r₂ := eq200 X0 (k X1 X1)
       grind)
    | (have r₁ := eq1433 X0 X1
       have r₂ := eq200 X0 X1
       grind)
    | (have r₁ := eq1433 X0 (M.op X0 X0)
       have r₂ := eq200 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1433 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq1433
  have eq1448 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1436 X0 X1
       have j1 := eq241 X0 X1
       grind)
    | (have r₁ := eq1436 X0 X1
       have r₂ := eq241 X0 (k X1 X1)
       grind)
    | (have r₁ := eq1436 X0 X1
       have r₂ := eq241 X0 X1
       grind)
    | (have r₁ := eq1436 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)
       have r₂ := eq241 X0 (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0)
       grind)
    | exact resolve eq1436 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1436
  have eq1449 : ∀ X0 X1 : G, (k X1 X1) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0 X1
    first
    | (have j0 := eq1437 X0 X1
       have j1 := eq216 X0 X1
       grind)
    | (have r₁ := eq1437 X0 X1
       have r₂ := eq216 X0 (k X1 X1)
       grind)
    | (have r₁ := eq1437 X0 X1
       have r₂ := eq216 X0 X1
       grind)
    | (have r₁ := eq1437 X0 (M.op (M.op (M.op x y) y) X0)
       have r₂ := eq216 X0 (M.op (M.op (M.op x y) y) X0)
       grind)
    | exact resolve eq1437 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq1437
  have eq1492 : ∀ X0 X2 : G, (k X2 X2) = (k X0 X0) := by
    intro X0 X2
    first
    | (have i₁ := eq1445 x X0
       have i₂ := eq1445 x X2
       grind)
    | exact superpose eq1445 eq1445
    | exact resolve eq1445 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1445 X0 (σ X1)
       grind)
    | exact superpose eq1445 eq10
    | exact resolve eq10 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X1 (σ X1)
       have i₂ := eq1445 X0 (σ X1)
       grind)
    | exact superpose eq1445 eq477
    | exact resolve eq477 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1565 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X1 X1
       have i₂ := eq1445 X0 (τ X1)
       grind)
    | exact superpose eq1445 eq504
    | exact resolve eq504 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq1566 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1445 X0 (τ X1)
       grind)
    | exact superpose eq1445 eq34
    | exact resolve eq34 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq1569 : ∀ X0 X1 : G, (k X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1566 X0 X1
       have i₂ := eq14 X1
       grind)
    | exact superpose eq14 eq1566
    | exact resolve eq1566 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1570 : ∀ X0 X1 : G, (k X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1564 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1564
    | exact resolve eq1564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1626 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133
       have i₂ := eq1492 X0 sF1
       grind)
    | (have i₁ := eq133
       have i₂ := eq1492 sF1 x
       grind)
    | exact superpose eq1492 eq133
    | exact resolve eq133 eq1492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1492
  have eq1706 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1563 X1 (M.op X0 X0)
       have i₂ := eq1298 X0
       grind)
    | exact superpose eq1298 eq1563
    | exact resolve eq1563 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1888 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq1570 X2 x
       have i₂ := eq1570 X0 x
       grind)
    | exact superpose eq1570 eq1570
    | exact resolve eq1570 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1935 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1298 X1
       have i₂ := eq1570 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1570 eq1298
    | exact resolve eq1298 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1937 : ∀ X0 X1 : G, (k X1 (τ (σ X1))) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq477 X1 (σ X1)
       have i₂ := eq1570 X0 (σ X1)
       grind)
    | exact superpose eq1570 eq477
    | exact resolve eq477 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1948 : ∀ X0 X1 : G, (k X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1937 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq1937
    | exact resolve eq1937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1988 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1565 X1 x
       have i₂ := eq1570 X0 x
       grind)
    | exact superpose eq1570 eq1565
    | exact resolve eq1565 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq2643 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq262 (M.op sF4 sF3) X1 x
       have i₂ := eq1706 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq1706 eq262
    | exact resolve eq262 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq4535 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1888 X1 x
       have i₂ := eq1935 X0 x
       grind)
    | exact superpose eq1935 eq1888
    | exact resolve eq1888 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5002 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1626 x
       have i₂ := eq1948 X0 x
       grind)
    | exact superpose eq1948 eq1626
    | exact resolve eq1626 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq1948
  have eq5065 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X1
       have i₂ := eq1445 X0 X1
       grind)
    | exact superpose eq1445 eq1413
    | (have j0 := eq1413 X1
       grind)
    | (have r₁ := eq1413 (M.op X0 X0)
       have r₂ := eq1445 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1413 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq5068 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) y) X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X1
       have i₂ := eq1449 X0 X1
       grind)
    | exact superpose eq1449 eq1413
    | (have j0 := eq1413 X1
       grind)
    | (have r₁ := eq1413 (M.op (M.op (M.op x y) y) X0)
       have r₂ := eq1449 X0 (M.op (M.op (M.op x y) y) X0)
       grind)
    | exact resolve eq1413 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq1449
  have eq9375 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1935 X3 x
       have i₂ := eq2643 X0 x X1
       grind)
    | (have i₁ := eq1935 X0 (σ (M.op X0 X0))
       have i₂ := eq2643 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq2643 eq1935
    | exact resolve eq1935 eq2643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643
  have eq11161 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1355
       grind)
    | exact superpose eq1355 eq39
    | exact resolve eq39 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1355
  have eq11162 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11161
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11161
    | exact resolve eq11161 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11161
  have eq11164 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq11162
    | exact resolve eq11162 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11162
  have eq251842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11164 eq1356
    | exact resolve eq1356 eq11164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq11164
  have eq251855 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq251842
       have r₂ := eq27
       grind)
    | exact resolve eq251842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251842
  have eq251918 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq251855 eq1935
    | exact resolve eq1935 eq251855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq251855
  have eq252192 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq251918
    | exact resolve eq251918 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251918
  have eq252297 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq252192 x
       have j1 := eq5065 x x
       grind)
    | (have r₁ := eq252192 x
       have r₂ := eq5065 x x
       grind)
    | (have r₁ := eq252192 x
       have r₂ := eq5065 x x
       grind)
    | exact resolve eq252192 eq5065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5065 eq252192
  have eq252366 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq180 x X0 X1
       have i₂ := eq252297
       grind)
    | exact superpose eq252297 eq180
    | exact resolve eq180 eq252297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq252368 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 x
       have i₂ := eq252297
       grind)
    | exact superpose eq252297 eq181
    | exact resolve eq181 eq252297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252297
  have eq252677 : ∀ X1 : G, x = (M.op x X1) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq252368 eq252366
    | exact resolve eq252366 eq252368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252366 eq252368
  have eq262059 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq252677 y
       grind)
    | exact superpose eq252677 eq18
    | (have j1 := eq252677 y
       grind)
    | exact resolve eq18 eq252677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252677
  have eq262288 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq262059
  have eq262402 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq262288 eq1448
    | exact resolve eq1448 eq262288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq262476 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq262402
    | (have j0 := eq262402 X0 X1
       grind)
    | exact resolve eq262402 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262402
  have eq262522 : ∀ X0 X1 : G, (k X0 X0) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq262288 eq262476
    | exact resolve eq262476 eq262288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262476
  have eq263384 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq262522 eq26
    | (have j1 := eq262522 X0 (σ y)
       grind)
    | exact resolve eq26 eq262522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263671 : ∀ X0 : G, (σ x) = (k X0 X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq262288 eq263384
    | exact resolve eq263384 eq262288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262288 eq263384
  have eq265029 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq262522 x X1
       have i₂ := eq263671 x
       grind)
    | exact superpose eq263671 eq262522
    | exact resolve eq262522 eq263671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262522
  have eq265102 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq263671 sF3
       grind)
    | exact superpose eq263671 eq115
    | exact resolve eq115 eq263671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq265119 : ∀ X1 : G, (σ x) = (M.op (σ x) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | (have j0 := eq265029 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265029
  have eq265127 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq265102
    | exact resolve eq265102 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq265102
  have eq265495 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq263671 eq265127
    | exact resolve eq265127 eq263671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263671 eq265127
  have eq266211 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq265495
       grind)
    | exact superpose eq265495 eq18
    | exact resolve eq18 eq265495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266239 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq265495
  have eq270631 : (M.op x y) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq266211 eq265119
    | exact resolve eq265119 eq266211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265119 eq266211
  have eq270660 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq270631
  have eq270663 : x = (M.op x y) := by
    first
    | (have r₁ := eq270660
       have r₂ := eq266239
       grind)
    | exact resolve eq270660 eq266239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266239 eq270660
  have eq273215 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq270663
       grind)
    | exact superpose eq270663 eq18
    | exact resolve eq18 eq270663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq273216 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq270663
       grind)
    | exact superpose eq270663 eq22
    | exact resolve eq22 eq270663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq270663
  have eq273240 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq273216 eq20
    | exact resolve eq20 eq273216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273216
  have eq273320 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq273215
       have i₂ := eq11 y sF0
       grind)
    | exact superpose eq11 eq273215
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq273215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273361 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq273215 eq5068
    | (have j0 := eq5068 X0 X1
       grind)
    | exact resolve eq5068 eq273215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068 eq273215
  have eq273396 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq1412 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq273320
       have r₂ := eq1412 (M.op x y) y
       grind)
    | exact resolve eq273320 eq1412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412 eq273320
  have eq273397 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq273361 x (M.op x y)
       grind)
    | (have r₁ := eq273396
       have r₂ := eq273361 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq273396
       have r₂ := eq273361 y (M.op x y)
       grind)
    | exact resolve eq273396 eq273361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273361 eq273396
  have eq273410 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq273397 eq181
    | exact resolve eq181 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq273429 : ∀ X0 : G, (σ (M.op x y)) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq273397 eq1569
    | exact resolve eq1569 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq273430 : ∀ X0 : G, (k X0 X0) = (τ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq273397 eq1570
    | exact resolve eq1570 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq273431 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq273397 eq1706
    | exact resolve eq1706 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq273455 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq273397 eq1888
    | exact resolve eq1888 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq273461 : ∀ X0 : G, (M.op X0 X0) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq273397 eq1988
    | exact resolve eq1988 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq273516 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (τ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq273397 eq4535
    | exact resolve eq4535 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4535
  have eq273530 : (k (M.op x y) (M.op x y)) = (τ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq273397 eq5002
    | exact resolve eq5002 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002
  have eq273567 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (σ (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq273397 eq9375
    | exact resolve eq9375 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9375
  have eq273608 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq273397 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq273397
       grind)
    | exact resolve eq13 eq273397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273397
  have eq273634 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq273608
  have eq273646 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (σ (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq20 eq273567
    | (have j0 := eq273567 X0 X1
       grind)
    | exact resolve eq273567 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273567
  have eq273663 : (M.op x y) = (τ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq273634 eq273530
    | exact resolve eq273530 eq273634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273530 eq273634
  have eq273694 : (τ (M.op x y)) = (τ (τ (τ (M.op x y)))) := by
    first
    | (have i₁ := eq273455 x
       have i₂ := eq273461 x
       grind)
    | exact superpose eq273461 eq273455
    | exact resolve eq273455 eq273461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273455 eq273461
  have eq273708 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq273431
    | (have j0 := eq273431 X0
       grind)
    | exact resolve eq273431 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273431
  have eq273709 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq273429 x
       have i₂ := eq273430 x
       grind)
    | exact superpose eq273430 eq273429
    | exact resolve eq273429 eq273430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273429 eq273430
  have eq273715 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | exact superpose eq273240 eq273646
    | exact resolve eq273646 eq273240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273646
  have eq273755 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq273663 eq273694
    | exact resolve eq273694 eq273663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273663 eq273694
  have eq273764 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq273240 eq273708
    | exact resolve eq273708 eq273240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273240 eq273708
  have eq273765 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq273709
    | exact resolve eq273709 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq273709
  have eq273768 : ∀ X1 : G, (M.op (σ x) X1) = (τ (τ (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq273715 x X1
       have i₂ := eq273516 x
       grind)
    | exact superpose eq273516 eq273715
    | exact resolve eq273715 eq273516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273516 eq273715
  have eq273812 : (M.op x y) = (σ x) := by
    first
    | (have i₁ := eq273764 x
       have i₂ := eq273410 x
       grind)
    | exact superpose eq273410 eq273764
    | exact resolve eq273764 eq273410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273410 eq273764
  have eq273813 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq273755 eq273765
    | exact resolve eq273765 eq273755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273765
  have eq273816 : ∀ X1 : G, (τ (M.op x y)) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq273755 eq273768
    | exact resolve eq273768 eq273755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273768
  have eq273855 : ∀ X1 : G, (τ (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq273812 eq273816
    | exact resolve eq273816 eq273812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273816
  have eq273894 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq273755 eq273855
    | exact resolve eq273855 eq273755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273755 eq273855
  have eq273980 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq273812 eq26
    | exact resolve eq26 eq273812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq273812
  have eq274035 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq273894 eq273980
    | exact resolve eq273980 eq273894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273894 eq273980
  have eq274088 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq274035 eq27
    | exact resolve eq27 eq274035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq274035
  have eq274175 : False := by grind
  exact eq274175

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pxx_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq106 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq150 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq173 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq150 eq16
    | exact resolve eq16 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq211 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq173
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq173
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq213 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq211
  have eq292 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 x X1 X3
       have i₂ := eq56 x X0
       grind)
    | (have i₁ := eq57 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq56 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq391 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq680 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq391 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq391
    | exact resolve eq391 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq1602 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 (σ X1) X1
       grind)
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 X0 (σ X1)
       grind)
    | exact superpose eq58 eq89
    | exact resolve eq89 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1605 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq89
  have eq1646 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1605 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq1649 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1602 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1657 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1646 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq1646
    | (have j0 := eq1646 X0
       grind)
    | exact resolve eq1646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq9761 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 X2
       have i₂ := eq1649 X1 X0
       grind)
    | exact superpose eq1649 eq58
    | (have j1 := eq1649 X2 X0
       grind)
    | exact resolve eq58 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9850 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1649 X0 (τ X1)
       grind)
    | exact superpose eq1649 eq35
    | (have j1 := eq1649 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq9851 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq1649 X0 x
       grind)
    | exact superpose eq1649 eq44
    | (have j1 := eq1649 X0 x
       grind)
    | exact resolve eq44 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649
  have eq9905 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq9851 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9851
    | (have j0 := eq9851 X0
       grind)
    | exact resolve eq9851 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9851
  have eq9906 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9850 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9850
    | (have j0 := eq9850 X0 X1
       grind)
    | exact resolve eq9850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9850
  have eq9916 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9906 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq9906
    | (have j0 := eq9906 X0 X1
       grind)
    | exact resolve eq9906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9906
  have eq10336 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k (σ x) (σ x)) X2) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 X1 X0 X2
       have i₂ := eq9905 X1
       grind)
    | exact superpose eq9905 eq57
    | (have j1 := eq9905 X1
       grind)
    | exact resolve eq57 eq9905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10338 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq9905 X0
       grind)
    | exact superpose eq9905 eq58
    | (have j1 := eq9905 X1
       grind)
    | exact resolve eq58 eq9905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9905
  have eq10542 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9916 X1 (τ X0)
       have i₂ := eq680 X0 X0
       grind)
    | exact superpose eq680 eq9916
    | (have j0 := eq9916 X1 (τ (k X0 X0))
       grind)
    | exact resolve eq9916 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10556 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X0 X0) X3) ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X2 X1 X3
       have i₂ := eq9916 X2 X0
       grind)
    | exact superpose eq9916 eq57
    | (have j1 := eq9916 X1 (M.op (k X0 X0) X3)
       grind)
    | exact resolve eq57 eq9916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10558 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X1 X2
       have i₂ := eq9916 X1 X0
       grind)
    | exact superpose eq9916 eq58
    | (have j1 := eq9916 X2 X0
       grind)
    | exact resolve eq58 eq9916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10732 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9916 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9916
  have eq10787 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10732 X1 (τ X0)
       have i₂ := eq680 X0 X0
       grind)
    | exact superpose eq680 eq10732
    | (have j0 := eq10732 X1 (τ X0)
       grind)
    | exact resolve eq10732 eq680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq10732
  have eq11483 : ∀ X0 X1 : G, (k x x) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq10338 eq50
    | (have j1 := eq10338 X1 X1
       grind)
    | exact resolve eq50 eq10338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10338
  have eq11722 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq44
       have i₂ := eq10558 x X1 X0
       grind)
    | exact superpose eq10558 eq44
    | (have j1 := eq10558 x X1 x
       grind)
    | exact resolve eq44 eq10558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11730 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq106
       have i₂ := eq10558 y X1 X0
       grind)
    | exact superpose eq10558 eq106
    | (have j1 := eq10558 y X1 x
       grind)
    | exact resolve eq106 eq10558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq69940 : ∀ X0 X1 : G, (σ x) ≠ (M.op (k (σ x) (σ x)) X1) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq10336 X0 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10336
  have eq69960 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq69940 X0 (k sF2 sF2)
       have i₂ := eq58 (k sF2 sF2) X1
       grind)
    | (have i₁ := eq69940 X0 (k sF2 sF2)
       have i₂ := eq58 X0 (k sF2 sF2)
       grind)
    | exact superpose eq58 eq69940
    | (have j0 := eq69940 X1 X1
       grind)
    | exact resolve eq69940 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69940
  have eq76916 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10556 X1 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10556
  have eq76982 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76916 X2 X1 (k X1 X1)
       have i₂ := eq58 (k X1 X1) X0
       grind)
    | (have i₁ := eq76916 X2 X1 (k X1 X1)
       have i₂ := eq58 X0 (k X1 X1)
       grind)
    | exact superpose eq58 eq76916
    | (have j0 := eq76916 X2 X1 X2
       grind)
    | (have r₁ := eq76916 X0 (M.op X1 X1) (k (M.op X1 X1) (M.op X1 X1))
       have r₂ := eq58 (k (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq76916 X0 (M.op X0 X0) (k (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq58 X0 (k (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq76916 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq91533
    | exact resolve eq91533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91533
  have eq91545 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq91534
       have r₂ := eq28
       grind)
    | exact resolve eq91534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91534
  have eq91551 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq91545
  have eq91692 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq91551
    | exact resolve eq91551 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91551
  have eq93051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq91692 eq117
    | exact resolve eq117 eq91692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq91692
  have eq93065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq93051
  have eq93068 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq93065
       have r₂ := eq28
       grind)
    | exact resolve eq93065 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93065
  have eq93071 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq93068
       have i₂ := eq58 sF2 x
       grind)
    | (have i₁ := eq93068
       have i₂ := eq58 X0 sF2
       grind)
    | exact superpose eq58 eq93068
    | exact resolve eq93068 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93068
  have eq93583 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    grind
  have eq93586 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = y := by
    intro X0 X1
    first
    | (have i₁ := eq58 x X0
       have i₂ := eq93071 X1
       grind)
    | exact superpose eq93071 eq58
    | (have j1 := eq93071 X1
       grind)
    | exact resolve eq58 eq93071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93645 : ∀ X0 X1 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ x) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq11722 x X0
       have i₂ := eq93071 X1
       grind)
    | exact superpose eq93071 eq11722
    | (have j0 := eq11722 X0 X0
       have j1 := eq93071 X1
       grind)
    | exact resolve eq11722 eq93071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93710 : ∀ X0 : G, x ≠ y ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq93071 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93071
  have eq93716 : ∀ X1 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = (σ x) ∨ x = (M.op x x) := by
    intro X1
    first
    | (have j0 := eq93645 x X1
       have j1 := eq76982 x (σ x) X1
       grind)
    | (have r₁ := eq93645 x X1
       have r₂ := eq76982 x x x
       grind)
    | (have r₁ := eq93645 x x
       have r₂ := eq76982 x (σ x) x
       grind)
    | (have r₁ := eq93645 x X1
       have r₂ := eq76982 x x x
       grind)
    | exact resolve eq93645 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93645
  have eq93722 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq93583 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93583
    | (have j0 := eq93583 X0
       grind)
    | exact resolve eq93583 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93583
  have eq93724 : ∀ X1 : G, (σ y) = (k (σ x) (σ x)) ∨ (M.op X1 X1) = (σ x) ∨ x = (M.op x x) := by
    intro X1
    first
    | (have i₁ := eq93716 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq93716
    | (have j0 := eq93716 X1
       grind)
    | exact resolve eq93716 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93716
  have eq94501 : ∀ X0 X1 X2 : G, (σ x) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = (σ x) ∨ y = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11730 x X0
       have i₂ := eq93586 X2 X1
       grind)
    | exact superpose eq93586 eq11730
    | (have j0 := eq11730 X0 X0
       have j1 := eq93586 X0 X1
       grind)
    | exact resolve eq11730 eq93586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11730 eq93586
  have eq94574 : ∀ X0 X1 : G, (σ x) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq94501 X0 X1 X0
       have j1 := eq76982 X0 y X0
       grind)
    | (have r₁ := eq94501 X0 X1 x
       have r₂ := eq76982 X0 y x
       grind)
    | (have r₁ := eq94501 X0 X0 x
       have r₂ := eq76982 X0 (σ x) x
       grind)
    | (have r₁ := eq94501 X0 X1 X0
       have r₂ := eq76982 X0 y x
       grind)
    | exact resolve eq94501 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94501
  have eq94582 : ∀ X0 X1 : G, (σ x) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq94574 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq94574
    | (have j0 := eq94574 X0 X1
       grind)
    | exact resolve eq94574 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94574
  have eq95900 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq105
       have i₂ := eq93722 X0
       grind)
    | exact superpose eq93722 eq105
    | (have j1 := eq93722 X0
       grind)
    | exact resolve eq105 eq93722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93722
  have eq95930 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq21 eq95900
    | (have j0 := eq95900 X0
       grind)
    | exact resolve eq95900 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95900
  have eq95989 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ x) ∨ (σ x) = (M.op X2 X2) ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq93724 eq10558
    | (have j0 := eq10558 (σ y) X0 X2
       have j1 := eq93724 X1
       grind)
    | exact resolve eq10558 eq93724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93724
  have eq96014 : ∀ X0 X1 : G, x = (M.op x x) ∨ (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq95989 X0 X1 X1
       have j1 := eq76982 X0 x x
       grind)
    | (have r₁ := eq95989 X0 X1 x
       have r₂ := eq76982 X0 (σ y) x
       grind)
    | (have r₁ := eq95989 X0 X0 x
       have r₂ := eq76982 X0 (σ x) x
       grind)
    | (have r₁ := eq95989 X0 X1 X0
       have r₂ := eq76982 X0 (σ x) x
       grind)
    | exact resolve eq95989 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95989
  have eq98121 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ y) ∨ y = (M.op X2 X2) ∨ (σ x) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq94582 eq10558
    | (have j0 := eq10558 (σ x) X0 X2
       have j1 := eq94582 X2 X0
       grind)
    | exact resolve eq10558 eq94582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10558 eq94582
  have eq98143 : ∀ X0 X1 X2 : G, y = (M.op X2 X2) ∨ (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq98121 X0 X1 X2 X0
       have j1 := eq69960 X0 X0
       grind)
    | (have r₁ := eq98121 X0 X1 X2 x
       have r₂ := eq69960 X0 X1
       grind)
    | (have r₁ := eq98121 X0 X1 X2 X0
       have r₂ := eq69960 X0 X1
       grind)
    | exact resolve eq98121 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98121
  have eq191796 : ∀ X0 X1 X2 X3 : G, x = y ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ y) ∨ (σ y) = (M.op X2 X2) ∨ (σ x) = (M.op X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96014 X1 X0
       have i₂ := eq98143 X3 X2 x
       grind)
    | exact superpose eq98143 eq96014
    | (have j0 := eq96014 X1 X0
       have j1 := eq98143 X0 X1 X2
       grind)
    | exact resolve eq96014 eq98143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96014 eq98143
  have eq191862 : ∀ X0 X1 X2 : G, x = y ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ y) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq191796 X0 X1 X1 X0
       have j1 := eq69960 X0 X0
       grind)
    | (have r₁ := eq191796 X0 X1 X2 x
       have r₂ := eq69960 X0 X1
       grind)
    | (have r₁ := eq191796 X0 X1 X2 X0
       have r₂ := eq69960 X0 X1
       grind)
    | exact resolve eq191796 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191796
  have eq191931 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq191862 X0 X1 X1
       have j1 := eq76982 X0 (σ y) X1
       grind)
    | (have r₁ := eq191862 X0 X1 x
       have r₂ := eq76982 X0 (σ x) x
       grind)
    | (have r₁ := eq191862 X0 X0 x
       have r₂ := eq76982 X0 (σ y) x
       grind)
    | (have r₁ := eq191862 X0 X1 X0
       have r₂ := eq76982 X0 (σ y) x
       grind)
    | exact resolve eq191862 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191862
  have eq192338 : ∀ X1 X2 : G, (τ (σ y)) = (k x x) ∨ (M.op X1 X1) = (σ x) ∨ (σ x) = (M.op X2 X2) ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq11483 x X1
       have i₂ := eq191931 X2 x
       grind)
    | (have i₁ := eq11483 x X1
       have i₂ := eq191931 x X1
       grind)
    | exact superpose eq191931 eq11483
    | (have j0 := eq11483 x X1
       have j1 := eq191931 X1 X1
       grind)
    | exact resolve eq11483 eq191931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191931
  have eq192941 : ∀ X1 : G, (τ (σ y)) = (k x x) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X1
    first
    | (have j0 := eq192338 X1 X1
       have j1 := eq69960 x X1
       grind)
    | (have r₁ := eq192338 x x
       have r₂ := eq69960 x X1
       grind)
    | (have r₁ := eq192338 X1 x
       have r₂ := eq69960 x X1
       grind)
    | exact resolve eq192338 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192338
  have eq192972 : ∀ X1 : G, y = (k x x) ∨ (M.op X1 X1) = (σ x) ∨ x = y := by
    intro X1
    first
    | exact superpose eq30 eq192941
    | (have j0 := eq192941 X1
       grind)
    | exact resolve eq192941 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq192941
  have eq194205 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1657 x
       have i₂ := eq192972 x
       grind)
    | exact superpose eq192972 eq1657
    | (have j0 := eq1657 x
       have j1 := eq192972 (σ x)
       grind)
    | exact resolve eq1657 eq192972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657 eq192972
  have eq194244 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq194205 X0
       have i₂ := eq105
       grind)
    | exact superpose eq105 eq194205
    | (have j0 := eq194205 (σ x)
       grind)
    | exact resolve eq194205 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq194205
  have eq194284 : ∀ X0 : G, (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq194244 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq194244
    | (have j0 := eq194244 (σ x)
       grind)
    | exact resolve eq194244 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq194244
  have eq194294 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq194284 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq194284
    | (have j0 := eq194284 (σ x)
       grind)
    | exact resolve eq194284 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194284
  have eq194303 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq194294
    | (have j0 := eq194294 (σ x)
       grind)
    | exact resolve eq194294 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194294
  have eq194305 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq194303 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq194303
    | (have j0 := eq194303 (σ x)
       grind)
    | exact resolve eq194303 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194303
  have eq194307 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have j0 := eq194305 (σ x)
       have j1 := eq69960 x (σ x)
       grind)
    | (have r₁ := eq194305 x
       have r₂ := eq69960 (σ x) x
       grind)
    | (have r₁ := eq194305 x
       have r₂ := eq69960 x x
       grind)
    | exact resolve eq194305 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194305
  have eq194483 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq194307 eq95930
    | (have j0 := eq95930 X0
       grind)
    | exact resolve eq95930 eq194307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95930 eq194307
  have eq194492 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq194483 X0
       have j1 := eq93710 X0
       grind)
    | (have r₁ := eq194483 X0
       have r₂ := eq93710 X0
       grind)
    | exact resolve eq194483 eq93710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93710 eq194483
  have eq194495 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq194492 (σ x)
       have j1 := eq76982 x x x
       grind)
    | (have r₁ := eq194492 x
       have r₂ := eq76982 x (σ x) x
       grind)
    | (have r₁ := eq194492 x
       have r₂ := eq76982 x x x
       grind)
    | (have r₁ := eq194492 x
       have r₂ := eq76982 (σ x) (σ x) x
       grind)
    | exact resolve eq194492 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194492
  have eq194497 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq194495
       have r₂ := eq28
       grind)
    | exact resolve eq194495 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194495
  have eq194511 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq194497
       have i₂ := eq58 sF2 x
       grind)
    | (have i₁ := eq194497
       have i₂ := eq58 X0 sF2
       grind)
    | exact superpose eq58 eq194497
    | exact resolve eq194497 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194545 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  have eq194616 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (σ x)) ∨ (M.op X0 X0) = x ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq194497 eq11722
    | (have j0 := eq11722 X0 X0
       grind)
    | exact resolve eq11722 eq194497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194723 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq194616 x
       have j1 := eq76982 x x x
       grind)
    | (have r₁ := eq194616 x
       have r₂ := eq76982 x x x
       grind)
    | (have r₁ := eq194616 x
       have r₂ := eq76982 x x x
       grind)
    | exact resolve eq194616 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194616
  have eq194751 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq194511 X1
       have i₂ := eq58 x X0
       grind)
    | (have i₁ := eq194511 X1
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq194511
    | (have j0 := eq194511 X1
       grind)
    | exact resolve eq194511 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194854 : ∀ X0 X1 : G, (k x x) = (τ x) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq11483 x X0
       have i₂ := eq194511 X1
       grind)
    | exact superpose eq194511 eq11483
    | (have j0 := eq11483 X0 X0
       have j1 := eq194511 X0
       grind)
    | exact resolve eq11483 eq194511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194511
  have eq194962 : ∀ X0 : G, (k x x) = (τ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq194854 X0 X0
       have j1 := eq69960 X0 X0
       grind)
    | (have r₁ := eq194854 X0 x
       have r₂ := eq69960 X0 x
       grind)
    | (have r₁ := eq194854 X0 X0
       have r₂ := eq69960 X0 x
       grind)
    | exact resolve eq194854 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194854
  have eq195365 : ∀ X1 X2 : G, (k (σ x) (σ x)) = (σ (σ x)) ∨ (M.op X1 X1) = x ∨ x = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq11722 x X1
       have i₂ := eq194751 X2 x
       grind)
    | (have i₁ := eq11722 x X1
       have i₂ := eq194751 x X1
       grind)
    | exact superpose eq194751 eq11722
    | (have j0 := eq11722 x X1
       have j1 := eq194751 X1 X1
       grind)
    | exact resolve eq11722 eq194751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11722 eq194751
  have eq195941 : ∀ X1 : G, (k (σ x) (σ x)) = (σ (σ x)) ∨ (M.op X1 X1) = x := by
    intro X1
    first
    | (have j0 := eq195365 X1 X1
       have j1 := eq76982 x x X1
       grind)
    | (have r₁ := eq195365 x x
       have r₂ := eq76982 x x x
       grind)
    | (have r₁ := eq195365 X1 x
       have r₂ := eq76982 x x x
       grind)
    | exact resolve eq195365 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195365
  have eq196032 : (k x x) = (τ (σ (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq194723 eq50
    | exact resolve eq50 eq194723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196107 : (σ x) = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196032
       have i₂ := eq16 sF2
       grind)
    | exact superpose eq16 eq196032
    | exact resolve eq196032 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196032
  have eq196167 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (M.op X0 X0) = (τ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10542 x X0
       have i₂ := eq196107
       grind)
    | exact superpose eq196107 eq10542
    | (have j0 := eq10542 (σ x) X0
       grind)
    | exact resolve eq10542 eq196107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10542 eq196107
  have eq196204 : ∀ X0 : G, (M.op X0 X0) = x ∨ (M.op X0 X0) = (τ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq196167
    | (have j0 := eq196167 X0
       grind)
    | exact resolve eq196167 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq196167
  have eq196227 : ∀ X0 : G, (M.op X0 X0) = (τ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq196204 x
       have j1 := eq76982 X0 (τ x) X0
       grind)
    | (have r₁ := eq196204 X0
       have r₂ := eq76982 X0 x x
       grind)
    | (have r₁ := eq196204 X0
       have r₂ := eq76982 X0 (τ x) x
       grind)
    | (have r₁ := eq196204 X0
       have r₂ := eq76982 x x x
       grind)
    | exact resolve eq196204 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196204
  have eq197269 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (τ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq194962 X0
       grind)
    | exact superpose eq194962 eq44
    | (have j1 := eq194962 X0
       grind)
    | exact resolve eq44 eq194962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq197350 : ∀ X0 : G, x = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq197269 X0
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq197269
    | (have j0 := eq197269 X0
       grind)
    | exact resolve eq197269 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197269
  have eq197442 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ (σ x)) ∨ (σ x) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq197350 eq9761
    | (have j0 := eq9761 x X0 X2
       have j1 := eq197350 X0
       grind)
    | exact resolve eq9761 eq197350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9761 eq197350
  have eq197477 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ (σ x)) ∨ (σ x) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197442 X0 X1 X2
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq197442
    | (have j0 := eq197442 X0 X1 X0
       grind)
    | exact resolve eq197442 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197442
  have eq197499 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq197477 X0 X1 X0
       have j1 := eq69960 X0 X0
       grind)
    | (have r₁ := eq197477 X0 X1 x
       have r₂ := eq69960 X0 X1
       grind)
    | (have r₁ := eq197477 X0 X1 X0
       have r₂ := eq69960 X0 X1
       grind)
    | exact resolve eq197477 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197477
  have eq197519 : ∀ X0 : G, (k x x) = (τ (σ (σ x))) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq195941 eq50
    | (have j1 := eq195941 X0
       grind)
    | exact resolve eq50 eq195941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq195941
  have eq197592 : ∀ X0 : G, (σ x) = (k x x) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq197519 X0
       have i₂ := eq16 sF2
       grind)
    | exact superpose eq16 eq197519
    | (have j0 := eq197519 X0
       grind)
    | exact resolve eq197519 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197519
  have eq197661 : ∀ X0 X1 X2 : G, x ≠ (M.op (σ x) X0) ∨ (M.op X1 X1) = x ∨ x = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76916 X1 x X0
       have i₂ := eq197592 X2
       grind)
    | exact superpose eq197592 eq76916
    | (have j0 := eq76916 X1 x X2
       have j1 := eq197592 X1
       grind)
    | (have r₁ := eq76916 X0 x (k x x)
       have r₂ := eq197592 (k x x)
       grind)
    | exact resolve eq76916 eq197592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76916 eq197592
  have eq197681 : ∀ X0 X1 : G, x ≠ (M.op (σ x) X0) ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have j0 := eq197661 X0 X1 X1
       have j1 := eq76982 X0 x X1
       grind)
    | (have r₁ := eq197661 (σ x) X1 x
       have r₂ := eq76982 X0 x (σ x)
       grind)
    | (have r₁ := eq197661 X0 X0 x
       have r₂ := eq76982 X0 x x
       grind)
    | (have r₁ := eq197661 X0 X1 X0
       have r₂ := eq76982 X0 x x
       grind)
    | exact resolve eq197661 eq76982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76982 eq197661
  have eq199166 : (σ x) = (τ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq194497
       have i₂ := eq196227 sF2
       grind)
    | exact superpose eq196227 eq194497
    | exact resolve eq194497 eq196227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194497 eq196227
  have eq199199 : x = (M.op x x) ∨ (σ x) = (τ x) := by grind
  clear eq199166
  have eq199320 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) ∨ (σ x) = (τ x) := by
    intro X0 X1
    first
    | (have i₁ := eq57 x X0 X1
       have i₂ := eq199199
       grind)
    | exact superpose eq199199 eq57
    | exact resolve eq57 eq199199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199199
  have eq202418 : ∀ X1 X2 : G, (k x x) = (τ (σ (σ x))) ∨ (M.op X1 X1) = (σ x) ∨ (σ x) = (M.op X2 X2) := by
    intro X1 X2
    first
    | (have i₁ := eq11483 x X1
       have i₂ := eq197499 X2 x
       grind)
    | (have i₁ := eq11483 x X1
       have i₂ := eq197499 x X1
       grind)
    | exact superpose eq197499 eq11483
    | (have j0 := eq11483 x X1
       have j1 := eq197499 X1 X1
       grind)
    | exact resolve eq11483 eq197499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11483 eq197499
  have eq203054 : ∀ X1 : G, (k x x) = (τ (σ (σ x))) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | (have j0 := eq202418 X1 X1
       have j1 := eq69960 x X1
       grind)
    | (have r₁ := eq202418 x x
       have r₂ := eq69960 x X1
       grind)
    | (have r₁ := eq202418 X1 x
       have r₂ := eq69960 x X1
       grind)
    | exact resolve eq202418 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202418
  have eq203083 : ∀ X1 : G, (σ x) = (k x x) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | (have i₁ := eq203054 X1
       have i₂ := eq16 sF2
       grind)
    | exact superpose eq16 eq203054
    | (have j0 := eq203054 X1
       grind)
    | exact resolve eq203054 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203054
  have eq204486 : ∀ X0 X1 : G, (σ x) = (τ x) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq194962 X0
       have i₂ := eq203083 X1
       grind)
    | exact superpose eq203083 eq194962
    | (have j0 := eq194962 X0
       have j1 := eq203083 X0
       grind)
    | exact resolve eq194962 eq203083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194962 eq203083
  have eq204535 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ x) = (τ x) := by
    intro X0
    first
    | (have j0 := eq204486 X0 X0
       have j1 := eq69960 X0 X0
       grind)
    | (have r₁ := eq204486 X0 x
       have r₂ := eq69960 X0 x
       grind)
    | (have r₁ := eq204486 X0 X0
       have r₂ := eq69960 X0 x
       grind)
    | exact resolve eq204486 eq69960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69960 eq204486
  have eq204853 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (σ x) X2) ∨ (σ x) = (τ x) := by
    intro X0 X2
    first
    | (have i₁ := eq57 x X0 X2
       have i₂ := eq204535 x
       grind)
    | exact superpose eq204535 eq57
    | exact resolve eq57 eq204535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq204535
  have eq207587 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ x) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq199320 X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq199320
    | (have j0 := eq199320 X0 y
       grind)
    | exact resolve eq199320 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199320
  have eq208972 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ x) = (τ x) := by
    intro X0
    grind
  have eq236250 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (σ x) = (τ x) := by
    intro X0
    first
    | exact superpose eq27 eq204853
    | (have j0 := eq204853 X0 (σ y)
       grind)
    | exact resolve eq204853 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204853
  have eq238396 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (τ x) := by
    first
    | (have i₁ := eq213
       have i₂ := eq236250 sF1
       grind)
    | exact superpose eq236250 eq213
    | exact resolve eq213 eq236250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq236250
  have eq238558 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (τ x) := by
    first
    | (have r₁ := eq238396
       have r₂ := eq28
       grind)
    | exact resolve eq238396 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238396
  have eq243525 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (τ x) ∨ (σ x) = (τ x) := by
    first
    | exact superpose eq208972 eq238558
    | exact resolve eq238558 eq208972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208972 eq238558
  have eq243530 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (τ x) := by grind
  clear eq243525
  have eq243766 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (τ x) ∨ (σ x) = (τ x) := by
    first
    | exact superpose eq243530 eq207587
    | exact resolve eq207587 eq243530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207587 eq243530
  have eq243827 : (σ x) = (τ x) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq243766
  have eq244003 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (σ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq243827
       grind)
    | exact superpose eq243827 eq15
    | exact resolve eq15 eq243827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243827
  have eq244410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ (σ x)) := by
    first
    | exact superpose eq244003 eq15
    | exact resolve eq15 eq244003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244003
  have eq244480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (σ (σ x)) := by
    first
    | exact superpose eq21 eq244410
    | exact resolve eq244410 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244410
  have eq244481 : x = (σ (σ x)) := by
    first
    | (have r₁ := eq244480
       have r₂ := eq28
       grind)
    | exact resolve eq244480 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244480
  have eq244542 : (σ x) = (τ x) := by
    first
    | exact superpose eq244481 eq16
    | exact resolve eq16 eq244481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249201 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq194545 eq194723
    | exact resolve eq194723 eq194545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194545 eq194723
  have eq249239 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op x x) := by grind
  clear eq249201
  have eq249272 : x = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq244481 eq249239
    | exact resolve eq249239 eq244481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244481 eq249239
  have eq249323 : x = (M.op x x) := by
    first
    | (have j1 := eq197681 x x
       grind)
    | (have r₁ := eq249272
       have r₂ := eq197681 (σ x) x
       grind)
    | exact resolve eq249272 eq197681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197681 eq249272
  have eq249373 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq249323
       have i₂ := eq58 x X0
       grind)
    | (have i₁ := eq249323
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq249323
    | exact resolve eq249323 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq249432 : (k x x) = (M.op x x) := by grind
  have eq249650 : x = (k x x) := by
    first
    | (have i₁ := eq249432
       have i₂ := eq249323
       grind)
    | exact superpose eq249323 eq249432
    | exact resolve eq249432 eq249323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249323 eq249432
  have eq250564 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq292 (M.op sF4 sF3) X1 x
       have i₂ := eq249373 (M.op sF4 sF3)
       grind)
    | exact superpose eq249373 eq292
    | exact resolve eq292 eq249373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq250738 : ∀ X1 : G, x = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq250564 x X1
       have i₂ := eq249373 x
       grind)
    | exact superpose eq249373 eq250564
    | exact resolve eq250564 eq249373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250564
  have eq251203 : ∀ X0 : G, (τ x) ≠ (τ x) ∨ (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq10787 x X0
       have i₂ := eq249650
       grind)
    | exact superpose eq249650 eq10787
    | (have j0 := eq10787 x X0
       grind)
    | exact resolve eq10787 eq249650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10787 eq249650
  have eq251225 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have j0 := eq251203 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251203
  have eq251241 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq251225 X0
       have i₂ := eq244542
       grind)
    | exact superpose eq244542 eq251225
    | exact resolve eq251225 eq244542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244542 eq251225
  have eq251280 : x = (σ x) := by
    first
    | (have i₁ := eq251241 x
       have i₂ := eq249373 x
       grind)
    | exact superpose eq249373 eq251241
    | exact resolve eq251241 eq249373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249373 eq251241
  have eq251321 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq251280 eq27
    | exact resolve eq27 eq251280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq252065 : x = (M.op x y) := by
    first
    | (have i₁ := eq250738 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq250738
    | (have j0 := eq250738 y
       grind)
    | exact resolve eq250738 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq252737 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq252065 eq21
    | exact resolve eq21 eq252065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq252065
  have eq252997 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq252737
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq252737
    | exact resolve eq252737 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq252737
  have eq253110 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq251280 eq252997
    | exact resolve eq252997 eq251280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251280 eq252997
  have eq253614 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq251321
       have i₂ := eq250738 sF3
       grind)
    | exact superpose eq250738 eq251321
    | exact resolve eq251321 eq250738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250738 eq251321
  have eq253615 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq253614 eq28
    | exact resolve eq28 eq253614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq253614
  have eq253738 : False := by grind
  exact eq253738

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyy_pxy_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  clear eq25
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq13
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq58 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq105 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq105
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq116
    | exact resolve eq116 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq146 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq169 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq146 eq16
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq57 x X1 X3
       have i₂ := eq56 x X0
       grind)
    | (have i₁ := eq57 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq56 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq311 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 X0 X1 x
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq57 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq318 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq311 X0 X1 X2
       grind)
    | (have r₁ := eq311 X0 X1 X2
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq311 X1 X0 X2
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq311 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq558 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X1 (M.op X2 X2)
       have i₂ := eq318 X0 X2 (τ X1)
       grind)
    | exact superpose eq318 eq35
    | exact resolve eq35 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq1237 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 (σ X1) X1
       grind)
    | (have i₁ := eq89 X1 X1
       have i₂ := eq58 X0 (σ X1)
       grind)
    | exact superpose eq58 eq89
    | exact resolve eq89 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1278 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq10928 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1278 X0 (τ X1)
       grind)
    | exact superpose eq1278 eq35
    | (have j1 := eq1278 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq10931 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq146
       have i₂ := eq1278 X0 sF0
       grind)
    | exact superpose eq1278 eq146
    | (have j1 := eq1278 X0 (M.op x y)
       grind)
    | exact resolve eq146 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq10945 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq10949 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10931
    | (have j0 := eq10931 X0
       grind)
    | exact resolve eq10931 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10931
  have eq10952 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq10928 X0 X1
       have j1 := eq82 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq10928 X0 X1
       have r₂ := eq82 X0 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq10928 X0 X1
       have r₂ := eq82 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq10928 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10928
  have eq10979 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq10949 X0
       have j1 := eq82 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq10949 X0
       have r₂ := eq82 X0 (σ (M.op x y)) x
       grind)
    | (have r₁ := eq10949 X0
       have r₂ := eq82 X0 (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | exact resolve eq10949 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq10949
  have eq10982 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10952 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq10952
    | exact resolve eq10952 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10952
  have eq11213 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq10979 eq169
    | exact resolve eq169 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq11742 : ∀ X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq10982 x X1
       have i₂ := eq10979 x
       grind)
    | exact superpose eq10979 eq10982
    | exact resolve eq10982 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11799 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10982 X1 (σ (M.op x x))
       have i₂ := eq558 X0 (σ (M.op x x)) x
       grind)
    | exact superpose eq558 eq10982
    | exact resolve eq10982 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq10982
  have eq12715 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11742 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq11742
    | exact resolve eq11742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50689 : ∀ X0 X1 : G, (σ X1) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10945 X0 X1
       have i₂ := eq12715 X1
       grind)
    | exact superpose eq12715 eq10945
    | (have j0 := eq10945 X0 X1
       grind)
    | exact resolve eq10945 eq12715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10945 eq12715
  have eq50704 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50689 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq50689
    | (have r₁ := eq50689 X0 (τ (k (σ (M.op x y)) (σ (M.op x y))))
       have r₂ := eq15 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq50689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50689
  have eq50796 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50704 X0 X1
       have i₂ := eq11742 sF1
       grind)
    | exact superpose eq11742 eq50704
    | (have j0 := eq50704 X1 X2
       grind)
    | (have r₁ := eq50704 (k X1 X1) X1
       have r₂ := eq11742 X1
       grind)
    | (have r₁ := eq50704 (k (σ (M.op x y)) (σ (M.op x y))) X1
       have r₂ := eq11742 (σ (M.op x y))
       grind)
    | exact resolve eq50704 eq11742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11742
  have eq50797 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq10979 eq50704
    | (have j0 := eq50704 X1 X2
       grind)
    | (have r₁ := eq50704 (M.op X0 X0) X1
       have r₂ := eq10979 X0
       grind)
    | exact resolve eq50704 eq10979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10979 eq50704
  have eq67758 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq50797 x x y
       grind)
    | (have r₁ := eq117
       have r₂ := eq50797 y x x
       grind)
    | (have r₁ := eq117
       have r₂ := eq50797 x x x
       grind)
    | exact resolve eq117 eq50797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq67773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq67758 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq67758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67758
  have eq67774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq50797 x (σ x) (σ y)
       grind)
    | (have r₁ := eq67773
       have r₂ := eq50797 (σ y) (σ x) x
       grind)
    | (have r₁ := eq67773
       have r₂ := eq50797 (σ x) (σ x) x
       grind)
    | (have r₁ := eq67773
       have r₂ := eq50797 y x x
       grind)
    | exact resolve eq67773 eq50797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50797 eq67773
  have eq67785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq67774
    | exact resolve eq67774 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67774
  have eq67787 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq67785
       have r₂ := eq28
       grind)
    | exact resolve eq67785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67785
  have eq67838 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq67787 eq11213
    | exact resolve eq11213 eq67787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11213 eq67787
  have eq67905 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq67838
    | exact resolve eq67838 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq67838
  have eq67947 : x = (M.op y y) := by
    first
    | (have j1 := eq50796 x x y
       grind)
    | (have r₁ := eq67905
       have r₂ := eq50796 (M.op x y) x x
       grind)
    | exact resolve eq67905 eq50796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50796 eq67905
  have eq67962 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq67947
       have i₂ := eq58 y X0
       grind)
    | (have i₁ := eq67947
       have i₂ := eq58 X0 y
       grind)
    | exact superpose eq58 eq67947
    | exact resolve eq67947 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq67947
  have eq68825 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq11799 x X0
       have i₂ := eq67962 x
       grind)
    | exact superpose eq67962 eq11799
    | exact resolve eq11799 eq67962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11799
  have eq68988 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq284 (M.op sF4 sF3) X1 x
       have i₂ := eq67962 (M.op sF4 sF3)
       grind)
    | exact superpose eq67962 eq284
    | exact resolve eq284 eq67962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq69012 : ∀ X1 : G, x = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq68988 x X1
       have i₂ := eq67962 x
       grind)
    | exact superpose eq67962 eq68988
    | exact resolve eq68988 eq67962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68988
  have eq69109 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq68825 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq68825
    | (have j0 := eq68825 X0
       grind)
    | exact resolve eq68825 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68825
  have eq69278 : x = (σ x) := by
    first
    | (have i₁ := eq69109 x
       have i₂ := eq67962 x
       grind)
    | exact superpose eq67962 eq69109
    | exact resolve eq69109 eq67962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67962 eq69109
  have eq69961 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq69278 eq27
    | exact resolve eq27 eq69278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq72651 : x = (M.op x y) := by
    first
    | (have i₁ := eq69012 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69012
    | (have j0 := eq69012 y
       grind)
    | exact resolve eq69012 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq72944 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq72651 eq21
    | exact resolve eq21 eq72651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq72651
  have eq73093 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq72944
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq72944
    | exact resolve eq72944 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq72944
  have eq73163 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq69278 eq73093
    | exact resolve eq73093 eq69278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69278 eq73093
  have eq73679 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69961
       have i₂ := eq69012 sF3
       grind)
    | exact superpose eq69012 eq69961
    | exact resolve eq69961 eq69012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69012 eq69961
  have eq73680 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq73679 eq28
    | exact resolve eq28 eq73679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq73679
  have eq73709 : False := by grind
  exact eq73709

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyy_x_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op (M.op (M.op X0 X1) X1) X2) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X3 X4 X4 X5
       have i₂ := eq14 X4 X0 X1 X2
       grind)
    | (have i₁ := eq14 X0 (M.op (M.op X1 X2) X2) X3 X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq57 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq13
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq57 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X1) X2) ≠ X3 ∨ (M.op (M.op (M.op X0 X1) X1) X2) = (k X4 X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | (have i₁ := eq13 X0 (M.op (M.op X1 X2) X2)
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X2) X3)
       have r₂ := eq14 (M.op (M.op (M.op X1 X2) X2) X3) X1 X2 X3
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq98
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq98 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq128
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq129
    | exact resolve eq129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq153 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq191 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq295 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 x X1 X3
       have i₂ := eq55 x X0
       grind)
    | (have i₁ := eq56 (M.op (M.op (σ x) (σ y)) (σ y)) X1 x
       have i₂ := eq55 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq323 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq56 X0 X1 x
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq56 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq56 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq56 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq56 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq323 X0 X1 X2
       grind)
    | (have r₁ := eq323 X0 X1 X2
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq323 X1 X0 X2
       have r₂ := eq57 X0 X1
       grind)
    | exact resolve eq323 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq394 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq574 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X1 (M.op X2 X2)
       have i₂ := eq331 X0 X2 (τ X1)
       grind)
    | exact superpose eq331 eq34
    | exact resolve eq34 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq632 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq394
    | exact resolve eq394 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq920 : ∀ X0 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op x y) y) X0) = (M.op (M.op (M.op (M.op (M.op X2 X3) X3) X4) X5) X6) := by
    intro X0 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq52 X2 X3 X4 x X5 X6
       have i₂ := eq54 x X0
       grind)
    | (have i₁ := eq52 X0 x X2 (M.op (M.op x y) y) X4 X5
       have i₂ := eq54 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1152 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X3 (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq83 X0 X1 X2 (M.op (M.op (M.op X0 X1) X1) X2) X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq1669 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq111 X1 X1
       have i₂ := eq57 (σ X1) X1
       grind)
    | (have i₁ := eq111 X1 X1
       have i₂ := eq57 X0 (σ X1)
       grind)
    | exact superpose eq57 eq111
    | exact resolve eq111 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1695 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq111 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1717 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1669 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq11063 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1717 X0 (τ X1)
       grind)
    | exact superpose eq1717 eq34
    | (have j1 := eq1717 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq11066 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq153
       have i₂ := eq1717 X0 sF0
       grind)
    | exact superpose eq1717 eq153
    | (have j1 := eq1717 X0 (M.op x y)
       grind)
    | exact resolve eq153 eq1717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq11084 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq11066
    | (have j0 := eq11066 X0
       grind)
    | exact resolve eq11066 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11066
  have eq11087 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq11063 X0 X1
       have j1 := eq81 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq11063 X0 X1
       have r₂ := eq81 X0 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq11063 X0 X1
       have r₂ := eq81 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq11063 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11063
  have eq11114 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq11084 X0
       have j1 := eq81 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq11084 X0
       have r₂ := eq81 X0 (σ (M.op x y)) x
       grind)
    | (have r₁ := eq11084 X0
       have r₂ := eq81 X0 (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | exact resolve eq11084 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq11084
  have eq11117 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11087 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq11087
    | exact resolve eq11087 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11087
  have eq11134 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have i₁ := eq11114 x
       have i₂ := eq54 x X0
       grind)
    | (have i₁ := eq11114 (M.op (M.op x y) y)
       have i₂ := eq54 X0 (M.op (M.op x y) y)
       grind)
    | exact superpose eq54 eq11114
    | exact resolve eq11114 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq11202 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq56 x X0 X2
       have i₂ := eq11114 x
       grind)
    | exact superpose eq11114 eq56
    | exact resolve eq56 eq11114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11886 : ∀ X1 : G, (k X1 X1) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq11117 x X1
       have i₂ := eq11114 x
       grind)
    | exact superpose eq11114 eq11117
    | exact resolve eq11117 eq11114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11943 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11117 X1 (σ (M.op x x))
       have i₂ := eq574 X0 (σ (M.op x x)) x
       grind)
    | exact superpose eq574 eq11117
    | exact resolve eq11117 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq11944 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11117 X1 (τ X0)
       have i₂ := eq632 X0 X0
       grind)
    | exact superpose eq632 eq11117
    | exact resolve eq11117 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12148 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq153
       have i₂ := eq11117 X0 sF0
       grind)
    | exact superpose eq11117 eq153
    | exact resolve eq153 eq11117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq11117
  have eq12842 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11886 (τ X0)
       have i₂ := eq632 X0 X0
       grind)
    | exact superpose eq632 eq11886
    | exact resolve eq11886 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq11886
  have eq21156 : ∀ X2 X3 X4 X5 X6 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op (M.op (M.op X2 X3) X3) X4) X5) X6) := by
    intro X2 X3 X4 X5 X6
    first
    | exact superpose eq11134 eq920
    | exact resolve eq920 eq11134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq11134
  have eq21381 : ∀ X4 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) X4) := by
    intro X4
    first
    | (have i₁ := eq21156 (M.op x x) x x x X4
       have i₂ := eq21156 x x x x x
       grind)
    | exact superpose eq21156 eq21156
    | exact resolve eq21156 eq21156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21156
  have eq23915 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq191 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq27517 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1695 X0 X1
       have i₂ := eq11114 (σ X0)
       grind)
    | exact superpose eq11114 eq1695
    | (have j0 := eq1695 X0 X1
       grind)
    | exact resolve eq1695 eq11114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq38791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq130 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq38791
    | exact resolve eq38791 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38791
  have eq38797 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq38792
       have r₂ := eq27
       grind)
    | exact resolve eq38792 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38792
  have eq38799 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq38797
    | exact resolve eq38797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38797
  have eq38801 : ∀ X0 : G, x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq38799
       have i₂ := eq57 sF2 x
       grind)
    | (have i₁ := eq38799
       have i₂ := eq57 X0 sF2
       grind)
    | exact superpose eq57 eq38799
    | exact resolve eq38799 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38799
  have eq38926 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have i₁ := eq38801 X1
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq38801 X1
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq38801
    | (have j0 := eq38801 X1
       grind)
    | exact resolve eq38801 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38978 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12148 x
       have i₂ := eq38801 X0
       grind)
    | exact superpose eq38801 eq12148
    | (have j1 := eq38801 X0
       grind)
    | exact resolve eq12148 eq38801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38801
  have eq39007 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq38978 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38978
    | (have j0 := eq38978 X0
       grind)
    | exact resolve eq38978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38978
  have eq48161 : ∀ X0 : G, x ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have j0 := eq38926 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38926
  have eq48663 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq39007 eq12842
    | (have j1 := eq39007 X0
       grind)
    | exact resolve eq12842 eq39007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39007
  have eq48694 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq48663
    | (have j0 := eq48663 X0
       grind)
    | exact resolve eq48663 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48663
  have eq48723 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq48694 x
       have i₂ := eq11114 x
       grind)
    | exact superpose eq11114 eq48694
    | exact resolve eq48694 eq11114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48694
  have eq49378 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq48723 eq11944
    | exact resolve eq11944 eq48723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48723
  have eq49415 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq28 eq49378
    | exact resolve eq49378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49378
  have eq49419 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq49415 X0
       have j1 := eq48161 X0
       grind)
    | (have r₁ := eq49415 X0
       have r₂ := eq48161 X0
       grind)
    | exact resolve eq49415 eq48161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48161 eq49415
  have eq49548 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op x X2) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq56 x X0 X2
       have i₂ := eq49419 x
       grind)
    | exact superpose eq49419 eq56
    | exact resolve eq56 eq49419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49638 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12148 x
       have i₂ := eq49419 x
       grind)
    | exact superpose eq49419 eq12148
    | exact resolve eq12148 eq49419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49419
  have eq49854 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq49638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49638
    | exact resolve eq49638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49638
  have eq50726 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) X1) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq49854 eq11202
    | exact resolve eq11202 eq49854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11202 eq49854
  have eq55861 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq49548 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq49548
    | (have j0 := eq49548 X0 y
       grind)
    | exact resolve eq49548 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49548
  have eq56787 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11943 x X0
       have i₂ := eq55861 x
       grind)
    | exact superpose eq55861 eq11943
    | exact resolve eq11943 eq55861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11943 eq55861
  have eq57049 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq56787
    | (have j0 := eq56787 X0
       grind)
    | exact resolve eq56787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56787
  have eq84712 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq50726
    | (have j0 := eq50726 X0 (σ y)
       grind)
    | exact resolve eq50726 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50726
  have eq85699 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq57049 x
       have i₂ := eq84712 x
       grind)
    | exact superpose eq84712 eq57049
    | exact resolve eq57049 eq84712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57049 eq84712
  have eq85885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq85699
  have eq85997 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq85885
       have r₂ := eq27
       grind)
    | exact resolve eq85885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85885
  have eq86220 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85997 eq27
    | exact resolve eq27 eq85997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86222 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85997 eq93
    | (have r₁ := eq93
       have r₂ := eq85997
       grind)
    | exact resolve eq93 eq85997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq86236 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq86222
  have eq96131 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq86236 eq130
    | exact resolve eq130 eq86236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86236
  have eq96192 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq96131
  have eq96212 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq96192
       have r₂ := eq86220
       grind)
    | exact resolve eq96192 eq86220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86220 eq96192
  have eq96261 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96212
       have i₂ := eq57 sF2 x
       grind)
    | (have i₁ := eq96212
       have i₂ := eq57 X0 sF2
       grind)
    | exact superpose eq57 eq96212
    | exact resolve eq96212 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96277 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq96212 eq13
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq96212
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq96212
       grind)
    | exact resolve eq13 eq96212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96212
  have eq96377 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq96277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96277
  have eq96670 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq96261 X1
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq96261 X1
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq96261
    | (have j0 := eq96261 X1
       grind)
    | exact resolve eq96261 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96752 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12148 x
       have i₂ := eq96261 X0
       grind)
    | exact superpose eq96261 eq12148
    | (have j1 := eq96261 X0
       grind)
    | exact resolve eq12148 eq96261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96261
  have eq96848 : ∀ X0 : G, (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq96752 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq96752
    | (have j0 := eq96752 X0
       grind)
    | exact resolve eq96752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96752
  have eq96968 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq96377 eq130
    | exact resolve eq130 eq96377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq96377
  have eq97045 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq96968
  have eq97216 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12148 x
       have i₂ := eq97045
       grind)
    | exact superpose eq97045 eq12148
    | exact resolve eq12148 eq97045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97045
  have eq97311 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq97216
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97216
    | exact resolve eq97216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97216
  have eq98458 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq97311 eq21381
    | exact resolve eq21381 eq97311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97311
  have eq101923 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq98458
    | (have j0 := eq98458 (σ y)
       grind)
    | exact resolve eq98458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98458
  have eq102156 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq101923 eq85997
    | exact resolve eq85997 eq101923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101923
  have eq102157 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq102156
  have eq102201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq102157 eq26
    | exact resolve eq26 eq102157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102157
  have eq110430 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq102201
       have i₂ := eq57 sF2 x
       grind)
    | (have i₁ := eq102201
       have i₂ := eq57 X0 sF2
       grind)
    | exact superpose eq57 eq102201
    | exact resolve eq102201 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102201
  have eq111191 : ∀ X2 : G, (M.op (σ x) (σ y)) = (k X2 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X2
    first
    | (have i₁ := eq1152 x x (M.op (M.op x x) x) x
       have i₂ := eq110430 (M.op (M.op x x) x)
       grind)
    | exact superpose eq110430 eq1152
    | exact resolve eq1152 eq110430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152 eq110430
  have eq114334 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85997 eq111191
    | exact resolve eq111191 eq85997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85997 eq111191
  have eq114460 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq114334 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114334
  have eq117795 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f117795_14 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k X0 X0)) := by
      intro X0 X1
      grind
    have f117795_15 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
      intro X0
      grind
    have f117795_23 : ∀ X0 : G, (τ (σ X0)) = X0 := by
      intro X0
      grind
    have f117795_24 : (M.op X0 X0) ≠ (τ (σ y)) := by grind
    have f117795_25 : y ≠ (M.op x y) := by grind
    have f117795_26 : (σ (M.op x y)) ≠ (σ x) := by grind
    have f117795_27 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
      intro X0
      first
      | (have j0 := f117795_15 X0
         grind)
      | (have r₁ := f117795_15 X0
         have r₂ := f117795_25
         grind)
      | exact resolve f117795_15 f117795_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f117795_28 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
      intro X0
      first
      | (have j0 := f117795_27 X0
         grind)
      | (have r₁ := f117795_27 X0
         have r₂ := f117795_26
         grind)
      | exact resolve f117795_27 f117795_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f117795_29 : y ≠ (M.op X0 X0) := by
      first
      | (have i₁ := f117795_24
         have i₂ := f117795_23 y
         grind)
      | exact superpose f117795_23 f117795_24
      | exact resolve f117795_24 f117795_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f117795_31 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) := by
      intro X0
      first
      | (have i₁ := f117795_14 (σ y) X0
         have i₂ := f117795_28 (σ y)
         grind)
      | exact superpose f117795_28 f117795_14
      | exact resolve f117795_14 f117795_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f117795_34 : ∀ X0 : G, y = (M.op X0 X0) := by
      intro X0
      first
      | (have i₁ := f117795_31 X0
         have i₂ := f117795_23 y
         grind)
      | exact superpose f117795_23 f117795_31
      | exact resolve f117795_31 f117795_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f117795_36 : y ≠ y := by
      first
      | (have i₁ := f117795_29
         have i₂ := f117795_34 X0
         grind)
      | exact superpose f117795_34 f117795_29
      | (have r₁ := f117795_29
         have r₂ := f117795_34 X0
         grind)
      | exact resolve f117795_29 f117795_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f117795_38 : False := by grind
    exact f117795_38
  clear eq114460
  have eq117901 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq29 eq117795
    | exact resolve eq117795 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq117795
  have eq302036 : ∀ X0 : G, x ≠ (σ x) ∨ (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq96670 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96670
  have eq303244 : ∀ X0 : G, (σ x) = (τ (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq96848 eq12842
    | (have j1 := eq96848 X0
       grind)
    | exact resolve eq12842 eq96848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96848
  have eq303390 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq303244
    | (have j0 := eq303244 X0
       grind)
    | exact resolve eq303244 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303244
  have eq303422 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq303390 x
       have i₂ := eq11114 x
       grind)
    | exact superpose eq11114 eq303390
    | exact resolve eq303390 eq11114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11114 eq303390
  have eq304464 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq303422 eq11944
    | exact resolve eq11944 eq303422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11944 eq303422
  have eq304616 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq28 eq304464
    | exact resolve eq304464 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304464
  have eq304620 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq304616 X0
       have j1 := eq302036 X0
       grind)
    | (have r₁ := eq304616 X0
       have r₂ := eq302036 X0
       grind)
    | exact resolve eq304616 eq302036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302036 eq304616
  have eq305548 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op x X2) ∨ y = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq56 x X0 X2
       have i₂ := eq304620 x
       grind)
    | exact superpose eq304620 eq56
    | exact resolve eq56 eq304620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq305641 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12148 x
       have i₂ := eq304620 x
       grind)
    | exact superpose eq304620 eq12148
    | exact resolve eq12148 eq304620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304620
  have eq306065 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq305641
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq305641
    | exact resolve eq305641 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305641
  have eq309022 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq306065 eq21381
    | exact resolve eq21381 eq306065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21381 eq306065
  have eq320629 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq309022
    | (have j0 := eq309022 (σ y)
       grind)
    | exact resolve eq309022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309022
  have eq320895 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq320629 eq27
    | exact resolve eq27 eq320629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320629
  have eq546174 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq305548 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq305548
    | (have j0 := eq305548 X0 y
       grind)
    | exact resolve eq305548 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305548
  have eq547780 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117901 x
       have i₂ := eq546174 x
       grind)
    | exact superpose eq546174 eq117901
    | exact resolve eq117901 eq546174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117901 eq546174
  have eq548069 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq547780
  have eq548242 : y = (M.op x y) := by
    first
    | (have r₁ := eq548069
       have r₂ := eq320895
       grind)
    | exact resolve eq548069 eq320895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320895 eq548069
  have eq548500 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq548242 eq20
    | exact resolve eq20 eq548242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq548504 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq548242 eq92
    | (have r₁ := eq92
       have r₂ := eq548242
       grind)
    | exact resolve eq92 eq548242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq548736 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq548504
  have eq548909 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq548500
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq548500
    | exact resolve eq548500 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548500
  have eq548959 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq548909 eq26
    | exact resolve eq26 eq548909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678366 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq23915 y
       have i₂ := eq548736
       grind)
    | exact superpose eq548736 eq23915
    | (have j0 := eq23915 y
       grind)
    | exact resolve eq23915 eq548736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23915
  have eq678418 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27517 x y
       have i₂ := eq548736
       grind)
    | exact superpose eq548736 eq27517
    | (have j0 := eq27517 x y
       grind)
    | exact resolve eq27517 eq548736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27517 eq548736
  have eq678424 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq678418
  have eq678429 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq678366
  have eq678433 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678424
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq678424
    | exact resolve eq678424 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678424
  have eq678439 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678429
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq678429
    | exact resolve eq678429 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678429
  have eq678455 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678433
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq678433
    | exact resolve eq678433 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678433
  have eq678460 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq678439
    | exact resolve eq678439 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq678439
  have eq678475 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq548909 eq678455
    | exact resolve eq678455 eq548909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678455
  have eq678480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq548909 eq678460
    | exact resolve eq678460 eq548909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678460
  have eq678493 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq678475
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq678475
    | exact resolve eq678475 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678475
  have eq678495 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq678480
       have r₂ := eq27
       grind)
    | exact resolve eq678480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678480
  have eq678496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq548959 eq678493
    | exact resolve eq678493 eq548959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678493
  have eq678498 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq678496
       have r₂ := eq27
       grind)
    | exact resolve eq678496 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678496
  have eq679392 : (σ x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq678498 eq12842
    | exact resolve eq12842 eq678498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678498
  have eq679448 : x = (M.op x x) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq679392
    | exact resolve eq679392 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679392
  have eq679593 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | (have i₁ := eq12148 x
       have i₂ := eq679448
       grind)
    | exact superpose eq679448 eq12148
    | exact resolve eq12148 eq679448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12148 eq679448
  have eq679691 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (σ x) := by
    first
    | (have i₁ := eq679593
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq679593
    | exact resolve eq679593 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679593
  have eq685146 : (σ x) = (τ (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq679691 eq12842
    | exact resolve eq12842 eq679691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12842 eq679691
  have eq685220 : x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq685146
    | exact resolve eq685146 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq685146
  have eq685221 : x = (σ x) := by grind
  clear eq685220
  have eq685484 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq685221 eq548959
    | exact resolve eq548959 eq685221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548959
  have eq685491 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq685221 eq678495
    | exact resolve eq678495 eq685221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678495
  have eq685492 : x = (M.op x x) := by grind
  clear eq685491
  have eq686288 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq685492
       have i₂ := eq57 x X0
       grind)
    | (have i₁ := eq685492
       have i₂ := eq57 X0 x
       grind)
    | exact superpose eq57 eq685492
    | exact resolve eq685492 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq685492
  have eq687121 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq295 (M.op sF4 sF3) X1 x
       have i₂ := eq686288 (M.op sF4 sF3)
       grind)
    | exact superpose eq686288 eq295
    | exact resolve eq295 eq686288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295
  have eq687245 : ∀ X1 : G, x = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq687121 x X1
       have i₂ := eq686288 x
       grind)
    | exact superpose eq686288 eq687121
    | exact resolve eq687121 eq686288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686288 eq687121
  have eq694581 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq685484 eq687245
    | exact resolve eq687245 eq685484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685484
  have eq694641 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq687245 y
       grind)
    | exact superpose eq687245 eq18
    | (have j1 := eq687245 y
       grind)
    | exact resolve eq18 eq687245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq687245
  have eq694845 : x = y := by
    first
    | exact superpose eq548242 eq694641
    | exact resolve eq694641 eq548242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548242 eq694641
  have eq694982 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq694581 eq27
    | exact resolve eq27 eq694581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq694581
  have eq695205 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq694845
       grind)
    | exact superpose eq694845 eq24
    | exact resolve eq24 eq694845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq694845
  have eq695860 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq548909 eq695205
    | exact resolve eq695205 eq548909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548909 eq695205
  have eq696132 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq695860
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq695860
    | exact resolve eq695860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq695860
  have eq696345 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq685221 eq696132
    | exact resolve eq696132 eq685221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685221 eq696132
  have eq696478 : False := by grind
  exact eq696478

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq93 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq89 sF2
       grind)
    | exact superpose eq89 eq50
    | exact resolve eq50 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq93
       have i₂ := eq89 x
       grind)
    | exact superpose eq89 eq93
    | exact resolve eq93 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq93
  have eq104 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94
       have i₂ := eq58 sF2 x
       grind)
    | (have i₁ := eq94
       have i₂ := eq58 X0 sF2
       grind)
    | exact superpose eq58 eq94
    | exact resolve eq94 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq94
  have eq107 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq163 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq137
       have i₂ := eq107 y x
       grind)
    | exact superpose eq107 eq137
    | (have j1 := eq107 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq137 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq170 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq163
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq163
    | exact resolve eq163 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq171 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq170
    | exact resolve eq170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq215 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq171 eq107
    | (have j0 := eq107 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq107 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq171
  have eq216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq215
    | exact resolve eq215 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq219 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq216
       have r₂ := eq28
       grind)
    | exact resolve eq216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq242 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq219 eq30
    | exact resolve eq30 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq219
  have eq254 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq242
    | exact resolve eq242 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq242
  have eq255 : x = y := by grind
  clear eq254
  have eq258 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq19
    | exact resolve eq19 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq259 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq255
       grind)
    | exact superpose eq255 eq25
    | exact resolve eq25 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq255
  have eq268 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq259
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq259
    | exact resolve eq259 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq259
  have eq271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq268 eq27
    | exact resolve eq27 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq268
  have eq336 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq271 eq104
    | exact resolve eq104 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq271
  have eq342 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq336
       have i₂ := eq258
       grind)
    | exact superpose eq258 eq336
    | exact resolve eq336 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq336
  have eq359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq342 eq15
    | exact resolve eq15 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq360 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq359
    | exact resolve eq359 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq359
  have eq361 : False := by grind
  exact eq361

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyy_pxx_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq21
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
  have eq57 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X1 (M.op x x) x X4
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | (have i₁ := eq14 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq14 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq89 x
       grind)
    | exact superpose eq89 eq44
    | exact resolve eq44 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq93 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq89 sF2
       grind)
    | exact superpose eq89 eq50
    | exact resolve eq50 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq93
       have i₂ := eq89 x
       grind)
    | exact superpose eq89 eq93
    | exact resolve eq93 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq89 sF2
       grind)
    | exact superpose eq89 eq92
    | exact resolve eq92 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq98 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq95
       have i₂ := eq58 x X0
       grind)
    | (have i₁ := eq95
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq95
    | exact resolve eq95 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq104 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94
       have i₂ := eq58 sF2 x
       grind)
    | (have i₁ := eq94
       have i₂ := eq58 X0 sF2
       grind)
    | exact superpose eq58 eq94
    | exact resolve eq94 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq130
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq130
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq130 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq146 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq140
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq140
    | exact resolve eq140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq147 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq146
    | exact resolve eq146 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq214 : ∀ X0 X1 X2 : G, (M.op x x) = (τ (M.op (M.op (M.op X0 X1) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104 x
       have i₂ := eq14 x X0 X1 X2
       grind)
    | (have i₁ := eq104 (M.op (M.op X1 X2) X2)
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq14 eq104
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 X1 : G, (M.op x x) = (τ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq104 x
       have i₂ := eq57 X0 x X1
       grind)
    | (have i₁ := eq104 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq104
    | exact resolve eq104 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq57 X0 X1 x
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq57 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq57 eq13
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) x)
       have r₂ := eq57 X0 (M.op (M.op X0 X0) x) x
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq57 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq363 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq354 X0 X1 X2
       grind)
    | (have r₁ := eq354 X0 X1 X2
       have r₂ := eq58 X0 X1
       grind)
    | (have r₁ := eq354 X1 X0 X2
       have r₂ := eq58 X0 X1
       grind)
    | exact resolve eq354 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq354
  have eq440 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (M.op x y))) = (k (k X0 (σ X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq42
    | exact resolve eq42 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq42
  have eq501 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq517 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (k X4 (M.op X5 X5)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq363 x X5 X4
       have i₂ := eq14 x X0 X1 X2
       grind)
    | (have i₁ := eq363 (M.op (M.op X1 X2) X2) X1 X2
       have i₂ := eq14 X0 X1 X2 (M.op (M.op X1 X2) X2)
       grind)
    | exact superpose eq14 eq363
    | exact resolve eq363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq40549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq147 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq40550 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq40549
    | exact resolve eq40549 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40549
  have eq40561 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq40550
       have r₂ := eq28
       grind)
    | exact resolve eq40550 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40550
  have eq40567 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq40561 eq94
    | exact resolve eq94 eq40561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq40561
  have eq40700 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq40567
    | exact resolve eq40567 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40567
  have eq40701 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq40700
  have eq40723 : x = (τ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq40701
       grind)
    | exact superpose eq40701 eq104
    | exact resolve eq104 eq40701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40731 : ∀ X0 : G, x = (τ (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq348 x x
       have i₂ := eq40701
       grind)
    | exact superpose eq40701 eq348
    | exact resolve eq348 eq40701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348 eq40701
  have eq40842 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq40723
       grind)
    | exact superpose eq40723 eq15
    | exact resolve eq15 eq40723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40723
  have eq40877 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq40842
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40842
    | exact resolve eq40842 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40842
  have eq40880 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq40877 eq30
    | exact resolve eq30 eq40877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40877
  have eq40989 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq40880
    | exact resolve eq40880 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40880
  have eq40990 : x = (σ x) ∨ x = y := by grind
  clear eq40989
  have eq41005 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq40990 eq27
    | exact resolve eq27 eq40990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51048 : x = (τ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40731 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq40731
    | (have j0 := eq40731 y
       grind)
    | exact resolve eq40731 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51051 : x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq41005 eq40731
    | exact resolve eq40731 eq41005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40731 eq41005
  have eq51092 : x = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq51051
  have eq51106 : (σ x) = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51048 eq15
    | exact resolve eq15 eq51048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51048
  have eq51141 : (σ x) = (σ y) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq51106
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51106
    | exact resolve eq51106 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51106
  have eq51144 : y = (τ (σ x)) ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq51141 eq30
    | exact resolve eq30 eq51141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51141
  have eq51275 : x = y ∨ (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq51144
    | exact resolve eq51144 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51144
  have eq51276 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq51275
  have eq51352 : x = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq51276 eq40990
    | exact resolve eq40990 eq51276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40990 eq51276
  have eq51379 : x = (M.op x y) ∨ x = y := by grind
  clear eq51352
  have eq51389 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq51379 eq21
    | exact resolve eq21 eq51379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51379
  have eq51518 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq51389
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq51389
    | exact resolve eq51389 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51389
  have eq52056 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq51092 eq15
    | exact resolve eq15 eq51092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51092
  have eq52091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52056
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52056
    | exact resolve eq52056 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52056
  have eq52093 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq52091 eq28
    | exact resolve eq28 eq52091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52091
  have eq52138 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq52093
       have r₂ := eq51518
       grind)
    | exact resolve eq52093 eq51518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51518 eq52093
  have eq52142 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq52138 eq30
    | exact resolve eq30 eq52138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52138
  have eq52277 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq52142
    | exact resolve eq52142 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52142
  have eq52278 : x = y := by grind
  clear eq52277
  have eq52294 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq52278
       grind)
    | exact superpose eq52278 eq19
    | exact resolve eq19 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq52295 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq52278
       grind)
    | exact superpose eq52278 eq25
    | exact resolve eq25 eq52278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq52278
  have eq52401 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq52295
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq52295
    | exact resolve eq52295 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq52295
  have eq52416 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq52401 eq27
    | exact resolve eq27 eq52401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq52401
  have eq52610 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq104 x
       have i₂ := eq52294
       grind)
    | exact superpose eq52294 eq104
    | exact resolve eq104 eq52294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53575 : ∀ X0 X1 X2 X3 X4 : G, (τ (M.op (M.op (M.op X0 X1) X1) X2)) = (k X3 (τ (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq501 X3 (M.op X4 X4)
       have i₂ := eq517 X0 X1 X2 (σ X3) X4
       grind)
    | exact superpose eq517 eq501
    | exact resolve eq501 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq517
  have eq53576 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op (M.op X0 X1) X1) X2)) = (k X3 (M.op x x)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53575 X0 X1 X2 X3 x
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq53575
    | exact resolve eq53575 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq53575
  have eq53745 : ∀ X0 X1 X2 X3 : G, (τ (M.op (M.op (M.op X0 X1) X1) X2)) = (k X3 (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53576 X0 X1 X2 X3
       have i₂ := eq52294
       grind)
    | exact superpose eq52294 eq53576
    | exact resolve eq53576 eq52294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53576
  have eq53764 : ∀ X3 : G, (M.op x x) = (k X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq53745 x x x X3
       have i₂ := eq214 x x x
       grind)
    | exact superpose eq214 eq53745
    | exact resolve eq53745 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq53745
  have eq53773 : ∀ X3 : G, (M.op x y) = (k X3 (M.op x y)) := by
    intro X3
    first
    | (have i₁ := eq53764 X3
       have i₂ := eq52294
       grind)
    | exact superpose eq52294 eq53764
    | exact resolve eq53764 eq52294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52294 eq53764
  have eq53780 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq52610 eq15
    | exact resolve eq15 eq52610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52610
  have eq53821 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq53780
    | exact resolve eq53780 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq53780
  have eq54018 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (k (k X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq53773 eq440
    | exact resolve eq440 eq53773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq54029 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (k (k X0 (σ (M.op x y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53821 eq54018
    | exact resolve eq54018 eq53821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54018
  have eq54070 : (M.op x y) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq53773 eq54029
    | exact resolve eq54029 eq53773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53773 eq54029
  have eq54109 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq54070
       have i₂ := eq89 sF0
       grind)
    | exact superpose eq89 eq54070
    | exact resolve eq54070 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq54070
  have eq54144 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq54109
       have i₂ := eq98 sF0
       grind)
    | exact superpose eq98 eq54109
    | exact resolve eq54109 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq54109
  have eq57693 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54144 eq52416
    | exact resolve eq52416 eq54144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52416 eq54144
  have eq57695 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq57693 eq28
    | exact resolve eq28 eq57693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq57693
  have eq57740 : False := by grind
  exact eq57740

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxx_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq11 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (M.op X0 X1) := by
    intro X0 X1
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq15 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq13 (σ x) (σ y)
       grind)
    | exact superpose eq13 eq9
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq12 (σ x) (σ y)
       grind)
    | exact superpose eq12 eq9
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq16
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16
  have eq18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq15
    | exact resolve eq15 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15
  have eq19 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq17
       have i₂ := eq14 (σ x) X0
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (σ x) X0
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq17
       have i₂ := eq13 (σ x) X0
       grind)
    | (have i₁ := eq17
       have i₂ := eq13 (σ x) (σ x)
       grind)
    | exact superpose eq13 eq17
    | (have j1 := eq13 (σ x) X0
       grind)
    | (have r₁ := eq17
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq17 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq14 (σ x) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (σ x) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq13 (σ x) X0
       grind)
    | (have i₁ := eq18
       have i₂ := eq13 (σ x) (σ x)
       grind)
    | exact superpose eq13 eq18
    | (have j1 := eq13 (σ x) X0
       grind)
    | exact resolve eq18 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq29 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x X0)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 (σ X0)
       have i₂ := eq11 x X0
       grind)
    | exact superpose eq11 eq19
    | (have j0 := eq19 (σ X0)
       grind)
    | exact resolve eq19 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq34 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x X0)) ∨ (M.op (σ y) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0)
       have i₂ := eq11 x X0
       grind)
    | exact superpose eq11 eq24
    | (have j0 := eq24 (σ X0)
       grind)
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq39 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op x x) ≠ (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq29 X0
       have i₂ := eq14 x X0
       grind)
    | exact superpose eq14 eq29
    | (have j0 := eq29 X0
       have j1 := eq14 (σ x) (σ X0)
       grind)
    | exact resolve eq29 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq9
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq64 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ (k x y)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X1) ∨ (M.op X1 X1) = (k (σ x) X1) ∨ (M.op X1 X1) ≠ (M.op (σ x) X1) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0
       have i₂ := eq12 (σ y) (σ y)
       grind)
    | (have i₁ := eq25 X0
       have i₂ := eq12 X0 (σ y)
       grind)
    | exact superpose eq12 eq25
    | (have j0 := eq25 X1
       have j1 := eq12 X0 (σ y)
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq25 (σ x)
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq25 X1
       have r₂ := eq12 (σ x) X1
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq667 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq64 (σ x) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq668 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq667 X0
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq667
    | (have j0 := eq667 X0
       grind)
    | exact resolve eq667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq669 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq681 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (σ x) X0) = (k (σ x) (σ x)) ∨ (k (σ x) X0) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq669 (σ x)
       have i₂ := eq14 (σ x) x
       grind)
    | exact superpose eq14 eq669
    | (have j1 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq669 X0
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq669 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq690 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (σ x) X0) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq698 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (k (σ x) X0) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) X0) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq690 X0
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq690
    | (have j0 := eq690 X0
       grind)
    | exact resolve eq690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq699 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x X0)) ∨ (σ (k x X0)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x X0)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq698 (σ x)
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq698
    | (have j0 := eq698 (σ X0)
       grind)
    | exact resolve eq698 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq714 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x X0)) ∨ (σ (M.op x X0)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x X0)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq699 x
       have i₂ := eq12 x x
       grind)
    | exact superpose eq12 eq699
    | (have j0 := eq699 y
       have j1 := eq12 x X0
       grind)
    | (have r₁ := eq699 x
       have r₂ := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq699 X0
       have r₂ := eq12 (σ x) (σ X0)
       grind)
    | exact resolve eq699 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1187 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (k x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq714 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq1190 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1187
       have i₂ := eq12 (σ x) (σ y)
       grind)
    | exact superpose eq12 eq1187
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq1187
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq1187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1191 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (k x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq1190
  have eq1193 : (σ (M.op x y)) = (σ (k x x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1191
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq1191
    | exact resolve eq1191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq224945 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq29
    | (have j0 := eq29 x
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq1193
       grind)
    | exact resolve eq29 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq224954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq224945
  have eq224955 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq224954
  have eq224970 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17
       have i₂ := eq224955
       grind)
    | exact superpose eq224955 eq17
    | (have r₁ := eq17
       have r₂ := eq224955
       grind)
    | exact resolve eq17 eq224955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224955
  have eq225177 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq224970
  have eq225178 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq225177
  have eq225193 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17
       have i₂ := eq225178
       grind)
    | exact superpose eq225178 eq17
    | exact resolve eq17 eq225178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225178
  have eq225388 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq225193
  have eq225621 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq225388
       have i₂ := eq12 x y
       grind)
    | exact superpose eq12 eq225388
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq225388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225388
  have eq225622 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq225621
  have eq225623 : (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq225622
  have eq226217 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq225623
       grind)
    | exact superpose eq225623 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq225623
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq225623
       grind)
    | exact resolve eq13 eq225623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226236 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq225623
       grind)
    | exact superpose eq225623 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq225623
       grind)
    | exact resolve eq14 eq225623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225623
  have eq226255 : (M.op x y) = (k y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq226236
  have eq230923 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq226217 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226217
  have eq230924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq230923
  have eq231076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq230924
       grind)
    | exact superpose eq230924 eq9
    | (have r₁ := eq9
       have r₂ := eq230924
       grind)
    | exact resolve eq9 eq230924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230924
  have eq231522 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq231076
  have eq231794 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq14 (σ y) (σ y)
       have i₂ := eq231522
       grind)
    | exact superpose eq231522 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq231522
       grind)
    | exact resolve eq14 eq231522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231522
  have eq231795 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq231794
  have eq231913 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq231795
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq231795
    | exact resolve eq231795 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231795
  have eq231958 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq231913
       grind)
    | exact superpose eq231913 eq9
    | exact resolve eq9 eq231913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231913
  have eq232158 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op y y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq231958
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq231958
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq231958
       have r₂ := eq14 x y
       grind)
    | exact resolve eq231958 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231958
  have eq232187 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq232158
  have eq232196 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op X0 y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (k X0 y) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq232187
       have i₂ := eq12 X0 y
       grind)
    | (have i₁ := eq232187
       have i₂ := eq12 y y
       grind)
    | exact superpose eq12 eq232187
    | (have j1 := eq12 x y
       grind)
    | exact resolve eq232187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232187
  have eq243371 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq232196 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232196
  have eq243372 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq243371
  have eq243461 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq47
    | (have j0 := eq47 X0
       grind)
    | exact resolve eq47 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq243471 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243490 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq243472
  have eq243491 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq243471
  have eq243501 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (k (σ x) X0) ∨ (M.op X0 X0) ≠ (M.op (σ x) X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq243461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243461
  have eq246575 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq243491
       have i₂ := eq12 (σ x) (σ y)
       grind)
    | exact superpose eq12 eq243491
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq243491
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq243491 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246576 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq246575
  have eq246654 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq246576
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq246576
    | exact resolve eq246576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246576
  have eq261215 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) X0) = (k (σ x) (σ x)) ∨ (k (σ x) X0) ≠ (k (σ x) X0) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq243501 (σ x)
       have i₂ := eq14 (σ x) x
       grind)
    | exact superpose eq14 eq243501
    | (have j1 := eq14 (σ x) X0
       grind)
    | (have r₁ := eq243501 X0
       have r₂ := eq14 x y
       grind)
    | exact resolve eq243501 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243501
  have eq261224 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (k (σ x) X0) = (k (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq261215 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261215
  have eq261314 : ∀ X0 : G, (σ (M.op x y)) ≠ (k (σ x) X0) ∨ (k (σ x) X0) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq261224 X0
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq261224
    | (have j0 := eq261224 X0
       grind)
    | exact resolve eq261224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261224
  have eq267713 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x X0)) ∨ (σ (k x X0)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq261314 (σ x)
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq261314
    | (have j0 := eq261314 (σ X0)
       grind)
    | exact resolve eq261314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261314
  have eq270004 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq267713 y
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq267713
    | (have j0 := eq267713 y
       grind)
    | exact resolve eq267713 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267713
  have eq270030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq270004
  have eq270031 : (σ (M.op x y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq270030
  have eq270195 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq270031
       grind)
    | exact superpose eq270031 eq29
    | (have j0 := eq29 x
       grind)
    | (have r₁ := eq29 x
       have r₂ := eq270031
       grind)
    | exact resolve eq29 eq270031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq270031
  have eq270203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq270195
  have eq270204 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq270203
  have eq275614 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17
       have i₂ := eq246654
       grind)
    | exact superpose eq246654 eq17
    | (have r₁ := eq17
       have r₂ := eq246654
       grind)
    | exact resolve eq17 eq246654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246654
  have eq275711 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq275614
  have eq275712 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq275711
  have eq275893 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq275712
       grind)
    | exact superpose eq275712 eq9
    | exact resolve eq9 eq275712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275712
  have eq276587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq275893
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq275893
    | exact resolve eq275893 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275893
  have eq276617 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq276587
  have eq276618 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq276617
  have eq276969 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq276618
       have i₂ := eq14 (σ y) x
       grind)
    | exact superpose eq14 eq276618
    | (have j1 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq276618
       have r₂ := eq14 x y
       grind)
    | exact resolve eq276618 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277091 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 (σ y) (σ y)
       have i₂ := eq276618
       grind)
    | exact superpose eq276618 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq276618
       grind)
    | exact resolve eq14 eq276618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277092 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq276618
  have eq277093 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq277091
  have eq277210 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq277093
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq277093
    | exact resolve eq277093 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277093
  have eq277227 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq277210
       grind)
    | exact superpose eq277210 eq9
    | exact resolve eq9 eq277210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277447 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq277227
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq277227
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq277227
       have r₂ := eq14 x y
       grind)
    | exact resolve eq277227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277227
  have eq277474 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq277447
  have eq277645 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq277092
       have i₂ := eq277210
       grind)
    | exact superpose eq277210 eq277092
    | exact resolve eq277092 eq277210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277092 eq277210
  have eq277650 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq277645
  have eq279076 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j0 := eq276969 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276969
  have eq279406 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq279076
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq279076
    | exact resolve eq279076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279076
  have eq279413 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq279406
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq279406
    | exact resolve eq279406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279406
  have eq279479 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq277650
       have i₂ := eq279413
       grind)
    | exact superpose eq279413 eq277650
    | (have r₁ := eq277650
       have r₂ := eq279413
       grind)
    | exact resolve eq277650 eq279413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279553 : (σ (k y y)) ≠ (σ (k y y)) ∨ (k (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 (σ x) (σ x)
       have i₂ := eq279413
       grind)
    | exact superpose eq279413 eq14
    | (have r₁ := eq14 x y
       have r₂ := eq279413
       grind)
    | exact resolve eq14 eq279413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279413
  have eq279572 : (k (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq279553
  have eq279610 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) := by grind
  clear eq279479
  have eq279611 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq279610
  have eq279662 : (σ (k x x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq279572
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq279572
    | exact resolve eq279572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279572
  have eq279673 : (σ (M.op y y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op y y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq279662
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq279662
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq279662
       have r₂ := eq14 x y
       grind)
    | exact resolve eq279662 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279662
  have eq280048 : (σ (M.op y y)) = (σ (k x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq279673
  have eq280053 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) ≠ (M.op x x) := by
    first
    | (have i₁ := eq280048
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq280048
    | (have j1 := eq14 x x
       grind)
    | (have r₁ := eq280048
       have r₂ := eq14 x y
       grind)
    | exact resolve eq280048 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280048
  have eq280096 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq280053
  have eq280467 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq279611
       grind)
    | exact superpose eq279611 eq9
    | exact resolve eq9 eq279611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280548 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq243491
       have i₂ := eq279611
       grind)
    | exact superpose eq279611 eq243491
    | exact resolve eq243491 eq279611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243491
  have eq280555 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq270204
       have i₂ := eq279611
       grind)
    | exact superpose eq279611 eq270204
    | exact resolve eq270204 eq279611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270204
  have eq280595 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (k (σ x) (σ y)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq279611
       grind)
    | exact superpose eq279611 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq279611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279611
  have eq280608 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (k (σ x) (σ y)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq280595
  have eq280644 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (k y y)) := by grind
  clear eq280555
  have eq280651 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq280548
  have eq280693 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ (k x y)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq280608
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq280608
    | exact resolve eq280608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280608
  have eq280705 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq280467
       have i₂ := eq226255
       grind)
    | exact superpose eq226255 eq280467
    | exact resolve eq280467 eq226255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226255
  have eq280706 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op y y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq280467
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq280467
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq280467
       have r₂ := eq14 x y
       grind)
    | exact resolve eq280467 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280735 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq280706
  have eq280736 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by grind
  clear eq280705
  have eq280737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq280736
  have eq280746 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq280735
       have i₂ := eq280096
       grind)
    | exact superpose eq280096 eq280735
    | exact resolve eq280735 eq280096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280750 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq280746
  have eq285607 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (k y y)) ∨ (σ (k x y)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq280644
       have i₂ := eq280693
       grind)
    | exact superpose eq280693 eq280644
    | (have r₁ := eq280644
       have r₂ := eq280693
       grind)
    | exact resolve eq280644 eq280693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280644
  have eq285608 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq280651
       have i₂ := eq280693
       grind)
    | exact superpose eq280693 eq280651
    | (have r₁ := eq280651
       have r₂ := eq280693
       grind)
    | exact resolve eq280651 eq280693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280651 eq280693
  have eq285718 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (k y y)) := by grind
  clear eq285608
  have eq285719 : (σ (k x y)) = (σ (k y y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq285718
  have eq285720 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (k y y)) := by grind
  clear eq285607
  have eq285721 : (σ (k x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq285720
  have eq285785 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op y y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq285721
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq285721
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq285721
       have r₂ := eq14 x y
       grind)
    | exact resolve eq285721 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285721
  have eq286172 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq285785
  have eq286410 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq286172
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq286172
    | exact resolve eq286172 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286172
  have eq286469 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq286410
  have eq286595 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq286469
       have i₂ := eq280096
       grind)
    | exact superpose eq280096 eq286469
    | exact resolve eq286469 eq280096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280096
  have eq286799 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq277474
       have i₂ := eq286469
       grind)
    | exact superpose eq286469 eq277474
    | (have r₁ := eq277474
       have r₂ := eq286469
       grind)
    | exact resolve eq277474 eq286469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286469
  have eq286849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq286799
  have eq286850 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq286849
  have eq287104 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq286595
  have eq288529 : ∀ X0 : G, (σ (M.op y y)) = (k (σ y) X0) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq286850
       have i₂ := eq14 (σ y) x
       grind)
    | exact superpose eq14 eq286850
    | (have j1 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq286850
       have r₂ := eq14 x y
       grind)
    | exact resolve eq286850 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286850
  have eq312854 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq285719
  have eq313228 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq312854
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq312854
    | exact resolve eq312854 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312854
  have eq313267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq313228
  have eq313268 : (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq313267
  have eq313761 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq280467
       have i₂ := eq313268
       grind)
    | exact superpose eq313268 eq280467
    | (have r₁ := eq280467
       have r₂ := eq313268
       grind)
    | exact resolve eq280467 eq313268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280467 eq313268
  have eq313830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq313761
  have eq313831 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq313830
  have eq314272 : ∀ X0 : G, (k (σ y) X0) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) X0) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq313831
       have i₂ := eq14 (σ y) x
       grind)
    | exact superpose eq14 eq313831
    | (have j1 := eq14 (σ y) X0
       grind)
    | (have r₁ := eq313831
       have r₂ := eq14 x y
       grind)
    | exact resolve eq313831 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313831
  have eq321440 : ∀ X0 : G, (σ (M.op x y)) = (σ (k y X0)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y X0)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq314272 (σ x)
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq314272
    | (have j0 := eq314272 (σ X0)
       grind)
    | exact resolve eq314272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314272
  have eq324814 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq280750
       have i₂ := eq287104
       grind)
    | exact superpose eq287104 eq280750
    | (have r₁ := eq280750
       have r₂ := eq287104
       grind)
    | exact resolve eq280750 eq287104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280750 eq287104
  have eq324834 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq324814
  have eq324835 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq324834
  have eq325011 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq324835
       grind)
    | exact superpose eq324835 eq9
    | exact resolve eq9 eq324835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325284 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 (σ x) (σ y)
       have i₂ := eq324835
       grind)
    | exact superpose eq324835 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq324835
       grind)
    | exact resolve eq14 eq324835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325522 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq325284
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq325284
    | exact resolve eq325284 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325284
  have eq331522 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq14 (σ y) X0
       have i₂ := eq288529 X0
       grind)
    | exact superpose eq288529 eq14
    | (have j0 := eq14 (σ y) X0
       have j1 := eq288529 X0
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq288529 X0
       grind)
    | exact resolve eq14 eq288529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288529
  have eq331562 : ∀ X0 : G, (M.op (σ y) (σ y)) ≠ (M.op (σ y) X0) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (k (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq331522 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331522
  have eq335180 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y X0)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq321440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321440
  have eq336534 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (k y X0)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) ∨ (M.op y y) ≠ (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq335180 X0
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq335180
    | (have j0 := eq335180 X0
       have j1 := eq14 (σ y) (σ X0)
       grind)
    | (have r₁ := eq335180 X0
       have r₂ := eq14 x y
       grind)
    | exact resolve eq335180 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335180
  have eq336604 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (k y X0)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq336534 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336534
  have eq345518 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have j0 := eq331562 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331562
  have eq345644 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq345518
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq345518
    | exact resolve eq345518 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345518
  have eq345722 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq277650
       have i₂ := eq345644
       grind)
    | exact superpose eq345644 eq277650
    | (have r₁ := eq277650
       have r₂ := eq345644
       grind)
    | exact resolve eq277650 eq345644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345644
  have eq345854 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq345722
  have eq345855 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq345854
  have eq347661 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq345855
  have eq347955 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op y y) ≠ (M.op y y) := by
    first
    | (have i₁ := eq347661
       have i₂ := eq14 y y
       grind)
    | exact superpose eq14 eq347661
    | (have j1 := eq14 y y
       grind)
    | (have r₁ := eq347661
       have r₂ := eq14 x y
       grind)
    | exact resolve eq347661 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347661
  have eq348063 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq347955
  have eq348408 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq243490
       have i₂ := eq348063
       grind)
    | exact superpose eq348063 eq243490
    | exact resolve eq243490 eq348063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243490
  have eq348482 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (σ (M.op y y)) = (k X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq348063
       grind)
    | exact superpose eq348063 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq348063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348649 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq348408
  have eq369008 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq348482 (σ x)
       have i₂ := eq324835
       grind)
    | exact superpose eq324835 eq348482
    | (have j0 := eq348482 (σ x)
       grind)
    | (have r₁ := eq348482 (σ x)
       have r₂ := eq324835
       grind)
    | exact resolve eq348482 eq324835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324835
  have eq369022 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by grind
  clear eq369008
  have eq369023 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by grind
  clear eq369022
  have eq369079 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq369023
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq369023
    | exact resolve eq369023 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369023
  have eq380317 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq325522
       have i₂ := eq369079
       grind)
    | exact superpose eq369079 eq325522
    | (have r₁ := eq325522
       have r₂ := eq369079
       grind)
    | exact resolve eq325522 eq369079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325522 eq369079
  have eq380367 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq380317
  have eq380368 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq380367
  have eq380524 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq380368
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq380368
    | exact resolve eq380368 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380368
  have eq380661 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq380524
  have eq380960 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq325011
       have i₂ := eq380661
       grind)
    | exact superpose eq380661 eq325011
    | (have r₁ := eq325011
       have r₂ := eq380661
       grind)
    | exact resolve eq325011 eq380661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325011 eq380661
  have eq381060 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq380960
  have eq381061 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq381060
  have eq381756 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq348063
       have i₂ := eq381061
       grind)
    | exact superpose eq381061 eq348063
    | exact resolve eq348063 eq381061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381998 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq381756
  have eq382459 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq277474
       have i₂ := eq381998
       grind)
    | exact superpose eq381998 eq277474
    | exact resolve eq277474 eq381998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277474 eq381998
  have eq382589 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq382459
  have eq434906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq280737
       grind)
    | exact superpose eq280737 eq9
    | (have r₁ := eq9
       have r₂ := eq280737
       grind)
    | exact resolve eq9 eq280737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280737
  have eq435039 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq434906
  have eq435107 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq435039
       have i₂ := eq348063
       grind)
    | exact superpose eq348063 eq435039
    | exact resolve eq435039 eq348063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435039
  have eq435497 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq435107
  have eq435718 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq280735
       have i₂ := eq435497
       grind)
    | exact superpose eq435497 eq280735
    | (have r₁ := eq280735
       have r₂ := eq435497
       grind)
    | exact resolve eq280735 eq435497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280735 eq435497
  have eq435858 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq435718
  have eq435859 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq435858
  have eq437448 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq435859
       grind)
    | exact superpose eq435859 eq9
    | exact resolve eq9 eq435859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437646 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq348649
       have i₂ := eq435859
       grind)
    | exact superpose eq435859 eq348649
    | (have r₁ := eq348649
       have r₂ := eq435859
       grind)
    | exact resolve eq348649 eq435859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348649
  have eq437675 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq348482 (σ x)
       have i₂ := eq435859
       grind)
    | exact superpose eq435859 eq348482
    | (have j0 := eq348482 (σ x)
       grind)
    | (have r₁ := eq348482 (σ x)
       have r₂ := eq435859
       grind)
    | exact resolve eq348482 eq435859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348482 eq435859
  have eq437691 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq437675
  have eq437692 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq437691
  have eq437719 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq437646
  have eq437720 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq437719
  have eq437939 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq437692
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq437692
    | exact resolve eq437692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437692
  have eq455326 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq437720
       have i₂ := eq437939
       grind)
    | exact superpose eq437939 eq437720
    | (have r₁ := eq437720
       have r₂ := eq437939
       grind)
    | exact resolve eq437720 eq437939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437720 eq437939
  have eq455352 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq455326
  have eq455353 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq455352
  have eq455511 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (k x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq437448
       have i₂ := eq455353
       grind)
    | exact superpose eq455353 eq437448
    | (have r₁ := eq437448
       have r₂ := eq455353
       grind)
    | exact resolve eq437448 eq455353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455353
  have eq455535 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op y y)) := by grind
  clear eq455511
  have eq455536 : (σ (k x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq455535
  have eq455717 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq455536
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq455536
    | exact resolve eq455536 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455536
  have eq455923 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq455717
  have eq456122 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq437448
       have i₂ := eq455923
       grind)
    | exact superpose eq455923 eq437448
    | (have r₁ := eq437448
       have r₂ := eq455923
       grind)
    | exact resolve eq437448 eq455923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437448 eq455923
  have eq456151 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq456122
  have eq456152 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq456151
  have eq456774 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq348063
       have i₂ := eq456152
       grind)
    | exact superpose eq456152 eq348063
    | exact resolve eq348063 eq456152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348063
  have eq456789 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq381061
       have i₂ := eq456152
       grind)
    | exact superpose eq456152 eq381061
    | exact resolve eq381061 eq456152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381061
  have eq457066 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq456789
  have eq457081 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq456774
  have eq457426 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq382589
       have i₂ := eq457066
       grind)
    | exact superpose eq457066 eq382589
    | (have r₁ := eq382589
       have r₂ := eq457066
       grind)
    | exact resolve eq382589 eq457066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382589 eq457066
  have eq457488 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq457426
  have eq457489 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq457488
  have eq457802 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (k y X0)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq336604 X0
       have i₂ := eq457081
       grind)
    | exact superpose eq457081 eq336604
    | (have j0 := eq336604 X0
       grind)
    | (have r₁ := eq336604 X0
       have r₂ := eq457081
       grind)
    | exact resolve eq336604 eq457081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336604 eq457081
  have eq457919 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ (k y X0)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq457802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457802
  have eq457920 : ∀ X0 : G, (σ (M.op x y)) = (σ (k y X0)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq457919 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457919
  have eq459580 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq456152
       have i₂ := eq457489
       grind)
    | exact superpose eq457489 eq456152
    | exact resolve eq456152 eq457489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456152
  have eq459688 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 (σ y) (σ y)
       have i₂ := eq457489
       grind)
    | exact superpose eq457489 eq14
    | (have j0 := eq14 (σ x) (σ x)
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq457489
       grind)
    | exact resolve eq14 eq457489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457489
  have eq459704 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq459688
  have eq459792 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq459580
  have eq460091 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq459704
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq459704
    | exact resolve eq459704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459704
  have eq460137 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17
       have i₂ := eq459792
       grind)
    | exact superpose eq459792 eq17
    | (have r₁ := eq17
       have r₂ := eq459792
       grind)
    | exact resolve eq17 eq459792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq459792
  have eq460416 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq460137
  have eq461799 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq277650
       have i₂ := eq460091
       grind)
    | exact superpose eq460091 eq277650
    | (have r₁ := eq277650
       have r₂ := eq460091
       grind)
    | exact resolve eq277650 eq460091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277650 eq460091
  have eq461987 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq461799
  have eq461988 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq461987
  have eq488210 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq460416
       grind)
    | exact superpose eq460416 eq9
    | exact resolve eq9 eq460416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460416
  have eq488631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq488210
       have i₂ := eq243372
       grind)
    | exact superpose eq243372 eq488210
    | exact resolve eq488210 eq243372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243372 eq488210
  have eq488829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq488631
  have eq488830 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq488829
  have eq489089 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq461988
       have i₂ := eq488830
       grind)
    | exact superpose eq488830 eq461988
    | exact resolve eq461988 eq488830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461988 eq488830
  have eq489282 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq489089
  have eq489497 : (σ (M.op x y)) ≠ (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq489282
       grind)
    | exact superpose eq489282 eq9
    | exact resolve eq9 eq489282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489282
  have eq489900 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq489497
       have i₂ := eq457920 y
       grind)
    | exact superpose eq457920 eq489497
    | (have j1 := eq457920 y
       grind)
    | (have r₁ := eq489497
       have r₂ := eq457920 y
       grind)
    | exact resolve eq489497 eq457920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457920 eq489497
  have eq489904 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
  clear eq489900
  have eq489905 : (M.op x y) = (M.op x x) := by grind
  clear eq489904
  have eq490011 : ∀ X0 : G, (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op x x) ≠ (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq489905
       grind)
    | exact superpose eq489905 eq39
    | (have j0 := eq39 X0
       grind)
    | (have r₁ := eq39 y
       have r₂ := eq489905
       grind)
    | exact resolve eq39 eq489905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq490167 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq489905
       grind)
    | exact superpose eq489905 eq14
    | (have j0 := eq14 x y
       grind)
    | (have r₁ := eq14 x y
       have r₂ := eq489905
       grind)
    | exact resolve eq14 eq489905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490168 : (k x y) = (M.op x x) := by grind
  clear eq490167
  have eq490285 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op x x) ≠ (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq490011 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490011
  have eq490321 : ∀ X0 : G, (M.op x x) ≠ (M.op x X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq490285 X0
       have i₂ := eq490168
       grind)
    | exact superpose eq490168 eq490285
    | (have j0 := eq490285 X0
       grind)
    | exact resolve eq490285 eq490168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490285
  have eq490651 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq490168
       grind)
    | exact superpose eq490168 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq490168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq490943 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq490651
       have i₂ := eq489905
       grind)
    | exact superpose eq489905 eq490651
    | exact resolve eq490651 eq489905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490651
  have eq490944 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by grind
  clear eq490943
  have eq642630 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j0 := eq490321 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490321
  have eq642631 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq642630
  have eq643016 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq642631
       grind)
    | exact superpose eq642631 eq9
    | exact resolve eq9 eq642631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642631
  have eq643450 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq643016
       have i₂ := eq489905
       grind)
    | exact superpose eq489905 eq643016
    | exact resolve eq643016 eq489905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643016
  have eq643451 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq643450
  have eq643846 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq14 (σ y) (σ y)
       have i₂ := eq643451
       grind)
    | exact superpose eq643451 eq14
    | exact resolve eq14 eq643451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643847 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq643846
  have eq643947 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq643847
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq643847
    | exact resolve eq643847 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643847
  have eq644079 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq643947
       have i₂ := eq13 (σ x) (σ y)
       grind)
    | exact superpose eq13 eq643947
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq643947 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644081 : (σ (M.op x y)) ≠ (σ (k y y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq643947
       grind)
    | exact superpose eq643947 eq9
    | exact resolve eq9 eq643947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644264 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq490944
       have i₂ := eq643947
       grind)
    | exact superpose eq643947 eq490944
    | exact resolve eq490944 eq643947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490944
  have eq644372 : (M.op (σ x) (σ y)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq644264
       have i₂ := eq643451
       grind)
    | exact superpose eq643451 eq644264
    | exact resolve eq644264 eq643451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644264
  have eq644417 : (σ (M.op x x)) ≠ (σ (k y y)) := by
    first
    | (have i₁ := eq644081
       have i₂ := eq489905
       grind)
    | exact superpose eq489905 eq644081
    | exact resolve eq644081 eq489905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489905 eq644081
  have eq644418 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq644079
       have i₂ := eq643451
       grind)
    | exact superpose eq643451 eq644079
    | (have r₁ := eq644079
       have r₂ := eq643451
       grind)
    | exact resolve eq644079 eq643451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644079
  have eq644432 : (σ (k y y)) ≠ (σ (k y y)) ∨ (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq644372
       have i₂ := eq643947
       grind)
    | exact superpose eq643947 eq644372
    | (have r₁ := eq644372
       have r₂ := eq643947
       grind)
    | exact resolve eq644372 eq643947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644372
  have eq644433 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) := by grind
  clear eq644432
  have eq644475 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq644418
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq644418
    | exact resolve eq644418 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644418
  have eq644478 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) ≠ (σ (k y y)) := by
    first
    | (have i₁ := eq644433
       have i₂ := eq643451
       grind)
    | exact superpose eq643451 eq644433
    | exact resolve eq644433 eq643451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644433
  have eq644508 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq644475
       have i₂ := eq490168
       grind)
    | exact superpose eq490168 eq644475
    | exact resolve eq644475 eq490168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490168 eq644475
  have eq644510 : (M.op (σ x) (σ x)) ≠ (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) := by
    first
    | (have i₁ := eq644478
       have i₂ := eq643947
       grind)
    | exact superpose eq643947 eq644478
    | exact resolve eq644478 eq643947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644478
  have eq644533 : (σ (M.op x x)) = (σ (k y y)) ∨ (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq644508
       have i₂ := eq643947
       grind)
    | exact superpose eq643947 eq644508
    | exact resolve eq644508 eq643947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643947 eq644508
  have eq644535 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (M.op (σ x) (σ x)) = (σ (k y y)) := by
    first
    | (have i₁ := eq644533
       have i₂ := eq643451
       grind)
    | exact superpose eq643451 eq644533
    | (have r₁ := eq644533
       have r₂ := eq643451
       grind)
    | exact resolve eq644533 eq643451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643451 eq644533
  have eq644536 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) := by grind
  clear eq644535
  have eq645600 : (σ (k y y)) ≠ (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) := by
    first
    | (have i₁ := eq644510
       have i₂ := eq644536
       grind)
    | exact superpose eq644536 eq644510
    | (have r₁ := eq644510
       have r₂ := eq644536
       grind)
    | exact resolve eq644510 eq644536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644510 eq644536
  have eq645702 : (σ (k y y)) ≠ (σ (k y y)) ∨ (σ (M.op x x)) = (σ (k y y)) := by grind
  clear eq645600
  have eq645703 : (σ (M.op x x)) = (σ (k y y)) := by grind
  clear eq645702
  have eq646210 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq644417
       have i₂ := eq645703
       grind)
    | exact superpose eq645703 eq644417
    | (have r₁ := eq644417
       have r₂ := eq645703
       grind)
    | exact resolve eq644417 eq645703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644417 eq645703
  have eq646260 : False := by grind
  exact eq646260
