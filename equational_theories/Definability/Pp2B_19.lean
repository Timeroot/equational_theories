import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pyx_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
    intro X0 X1 X2
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72 x y
       grind)
    | exact superpose eq72 eq44
    | (have j1 := eq72 x x
       grind)
    | exact resolve eq44 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq104
  have eq119 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq414 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq105 eq72
    | (have j0 := eq72 (σ x) x
       grind)
    | exact resolve eq72 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq690 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq689
    | exact resolve eq689 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq693 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq690
       have r₂ := eq27
       grind)
    | exact resolve eq690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq700 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq693 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq693
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq693
       grind)
    | exact resolve eq13 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq700 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq712 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq701 eq49
    | exact resolve eq49 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq701
  have eq730 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq693 eq712
    | exact resolve eq712 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693 eq712
  have eq743 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq730
  have eq745 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq743
    | exact resolve eq743 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq743
  have eq754 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72 x x
       have i₂ := eq745
       grind)
    | exact superpose eq745 eq72
    | (have j0 := eq72 x x
       grind)
    | exact resolve eq72 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq755 : x = (M.op x x) := by grind
  clear eq754
  have eq761 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 x
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq14
    | exact resolve eq14 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq755
       grind)
    | exact resolve eq13 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq763 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq766 : ∀ X0 : G, x = (M.op (M.op X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq761 X0
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq761
    | exact resolve eq761 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq779 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq764 x
       grind)
    | exact superpose eq764 eq43
    | exact resolve eq43 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq781 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq119
       have i₂ := eq764 sF0
       grind)
    | exact superpose eq764 eq119
    | exact resolve eq119 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq764
  have eq787 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq779
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq779
    | exact resolve eq779 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755 eq779
  have eq788 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq787
    | exact resolve eq787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq787
  have eq793 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq788 eq72
    | (have j0 := eq72 (σ x) x
       grind)
    | exact resolve eq72 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq788
  have eq794 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq793
  have eq804 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq794 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq794
       grind)
    | exact resolve eq13 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq805 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq877 : ∀ X0 : G, (M.op x (M.op X0 x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq414 X0 x X0
       have i₂ := eq766 X0
       grind)
    | exact superpose eq766 eq414
    | exact resolve eq414 eq766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq766
  have eq903 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq416 x
       have i₂ := eq877 sF0
       grind)
    | exact superpose eq877 eq416
    | exact resolve eq416 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq970 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op X0 X1) (M.op y (M.op x y)))) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq419
    | exact resolve eq419 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq419
  have eq1007 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op X0 X1) x)) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq903 eq970
    | exact resolve eq970 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq970
  have eq1021 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1007 X0 X1
       have i₂ := eq877 (M.op X0 X1)
       grind)
    | exact superpose eq877 eq1007
    | exact resolve eq1007 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq1007
  have eq1043 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1021 (M.op X1 X0) X1
       have i₂ := eq1021 X1 X0
       grind)
    | exact superpose eq1021 eq1021
    | exact resolve eq1021 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1021 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1021
    | (have j0 := eq1021 x y
       grind)
    | exact resolve eq1021 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1021
  have eq1284 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1047 eq781
    | exact resolve eq781 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781 eq1047
  have eq1285 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq805 eq1284
    | exact resolve eq1284 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq1284
  have eq1286 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1285
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1285
    | exact resolve eq1285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1285
  have eq1295 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1286 eq1043
    | exact resolve eq1043 eq1286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq1286
  have eq1296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1295
    | exact resolve eq1295 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1295
  have eq1303 : False := by grind
  exact eq1303

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_x_pxy_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  clear eq35
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X0 X2))) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 (M.op X2 (M.op X0 X2))) = (k (M.op X1 (M.op X2 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X0 X2))) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X0 X2))) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq128 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq206 : ∀ X0 X1 : G, x = (M.op X0 (M.op (M.op y (M.op x y)) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op y sF0) (M.op x (M.op X0 x)))
       have i₂ := eq14 X0 (M.op y sF0) x
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op x y))) = (M.op (M.op X0 (M.op X1 x)) X0) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op y (M.op x y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X1))) = (M.op (σ x) (M.op (M.op X0 X2) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq503 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op X0 X1) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) x X1 X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X0) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq52 X2 X0 X1 x
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) (M.op X4 (M.op X3 X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X3 (M.op X1 X2) X2 X4
       have i₂ := eq52 X1 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X2 (M.op (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X2))) = (M.op (M.op X5 X0) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X3 (M.op X0 X3)) (M.op X4 (M.op X1 X4))) X5 X1 X2
       have i₂ := eq53 X1 X3 X0 X4
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq90 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq688 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq687 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq790 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) ≠ X2 ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 (M.op X1 X2)) X0) = (k (M.op (M.op X0 (M.op X1 X2)) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 X2 x
       have i₂ := eq52 X0 X1 X2 x
       grind)
    | exact superpose eq52 eq74
    | (have j0 := eq74 X0 X1 X2
       grind)
    | (have r₁ := eq74 (M.op X2 (M.op x (M.op X0 x))) (M.op (M.op X2 (M.op (M.op X2 (M.op x (M.op X0 x))) X2)) (M.op X2 X0)) X2
       have r₂ := eq52 X0 (M.op X2 (M.op (M.op X2 (M.op x (M.op X0 x))) X2)) X2 x
       grind)
    | exact resolve eq74 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq74
  have eq799 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X1)) (M.op X3 (M.op X0 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq503 X2 (M.op X1 (M.op (M.op X0 X2) X1)) X3
       have i₂ := eq503 X0 X2 X1
       grind)
    | exact superpose eq503 eq503
    | exact resolve eq503 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X2 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq503
    | exact resolve eq503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op X0 x)) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq503
    | exact resolve eq503 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) X0)) := by
    intro X0
    first
    | exact superpose eq816 eq503
    | exact resolve eq503 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X0) (M.op X1 (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq508
    | exact resolve eq508 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : ∀ X0 : G, y = (M.op (M.op (M.op X0 (M.op x y)) X0) x) := by
    intro X0
    first
    | (have i₁ := eq508 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq508
    | (have j0 := eq508 X0 x y
       grind)
    | exact resolve eq508 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq508
    | (have j0 := eq508 X0 (σ x) (σ y)
       grind)
    | exact resolve eq508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq840 eq14
    | exact resolve eq14 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq1179 : ∀ X0 : G, (M.op (M.op X0 x) X0) = (M.op (M.op x (M.op y (M.op x y))) (M.op y (M.op x y))) := by
    intro X0
    first
    | exact superpose eq50 eq209
    | exact resolve eq209 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1206 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 x)) = (M.op X1 (M.op X2 (M.op (M.op X0 (M.op y (M.op x y))) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 (M.op X1 (M.op X0 x)) X1 X2
       have i₂ := eq209 X1 X0
       grind)
    | exact superpose eq209 eq503
    | exact resolve eq503 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op y (M.op x y)))) X1) (M.op X2 (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 X1 (M.op X2 (M.op X0 x)) X2
       have i₂ := eq209 X2 X0
       grind)
    | exact superpose eq209 eq508
    | exact resolve eq508 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op y (M.op x y))) (M.op (M.op X1 X2) (M.op X0 x))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq508 (M.op (M.op X1 X2) (M.op X0 x)) X1 X2
       have i₂ := eq209 (M.op X1 X2) X0
       grind)
    | exact superpose eq209 eq508
    | exact resolve eq508 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq1233 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op (M.op X0 (M.op x y)) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq875 eq814
    | exact resolve eq814 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq1234 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq879 eq814
    | exact resolve eq814 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1279 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq814 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq814
    | (have j0 := eq814 y X0 x
       grind)
    | exact resolve eq814 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq814
    | (have j0 := eq814 (σ y) X0 (σ x)
       grind)
    | exact resolve eq814 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1294 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X2 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq814 X1 X2 X0
       grind)
    | exact superpose eq814 eq503
    | exact resolve eq503 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1316 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op X0 (M.op (σ x) (σ y))) X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq26 eq1234
    | (have j0 := eq1234 X0 X1
       grind)
    | exact resolve eq1234 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1317 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op (M.op X0 (M.op x y)) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1233 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1233
    | (have j0 := eq1233 X0 X1
       grind)
    | exact resolve eq1233 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1233
  have eq1327 : ∀ X0 : G, (M.op (M.op y X0) (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq1279 eq503
    | exact resolve eq503 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2833 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq503 X2 X0 (M.op (M.op X1 X2) X1)
       have i₂ := eq1294 X1 X2 X0
       grind)
    | exact superpose eq1294 eq503
    | exact resolve eq503 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq2909 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq814 X0 X1 (M.op X0 sF4)
       grind)
    | exact superpose eq814 eq1316
    | exact resolve eq1316 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq3015 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1317 X0 (M.op X1 (M.op X0 X1))
       have i₂ := eq814 X0 X1 (M.op X0 sF0)
       grind)
    | exact superpose eq814 eq1317
    | exact resolve eq1317 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq1317
  have eq8875 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq688 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq688
    | (have j0 := eq688 (τ X0)
       grind)
    | exact resolve eq688 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq688
  have eq8883 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq8875 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8875
    | (have j0 := eq8875 X0
       grind)
    | exact resolve eq8875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8875
  have eq8889 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8883 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8883
    | (have j0 := eq8883 X0
       grind)
    | exact resolve eq8883 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8883
  have eq9002 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq483 (M.op X1 (M.op x X1)) sF0 y
       have i₂ := eq53 y X1 x sF0
       grind)
    | exact superpose eq53 eq483
    | exact resolve eq483 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq483
  have eq12107 : ∀ X0 : G, x = (M.op X0 (M.op (σ x) (M.op (M.op (M.op y (M.op x y)) X0) (M.op (σ y) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | (have i₁ := eq206 x x
       have i₂ := eq502 (M.op y sF0) x x
       grind)
    | exact superpose eq502 eq206
    | exact resolve eq206 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq502
  have eq25617 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq25682 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq25617
  have eq25688 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq25682
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq25682
    | exact resolve eq25682 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25682
  have eq25699 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq25688
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq25688 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25688
  have eq25707 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq25699 eq84
    | exact resolve eq84 eq25699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq62789 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq62789
    | exact resolve eq62789 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62789
  have eq62808 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq62797
       have r₂ := eq27
       grind)
    | exact resolve eq62797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62797
  have eq62810 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq62808
    | exact resolve eq62808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62808
  have eq62812 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq62810 eq25707
    | exact resolve eq25707 eq62810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62810
  have eq62933 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq62812
    | exact resolve eq62812 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62812
  have eq62939 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq8889 y
       grind)
    | (have r₁ := eq62933
       have r₂ := eq8889 y
       grind)
    | exact resolve eq62933 eq8889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62933
  have eq62946 : y = (M.op y (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1327 y
       have i₂ := eq62939
       grind)
    | exact superpose eq62939 eq1327
    | exact resolve eq1327 eq62939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq62947 : x = (M.op (M.op y y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1279 y
       have i₂ := eq62939
       grind)
    | exact superpose eq62939 eq1279
    | exact resolve eq1279 eq62939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62948 : (M.op y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq973 y
       have i₂ := eq62939
       grind)
    | exact superpose eq62939 eq973
    | exact resolve eq973 eq62939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq62949 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq62939
       grind)
    | exact superpose eq62939 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq62939
       grind)
    | exact resolve eq13 eq62939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63042 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq62949 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62949
  have eq63443 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62947
       have i₂ := eq62939
       grind)
    | exact superpose eq62939 eq62947
    | exact resolve eq62947 eq62939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62947
  have eq63546 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63443
  have eq64818 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62948 eq62946
    | exact resolve eq62946 eq62948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62946 eq62948
  have eq64924 : y = (M.op y (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64818
  have eq64974 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq63042 y
       grind)
    | exact superpose eq63042 eq70
    | exact resolve eq70 eq63042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64981 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq63042 sF0
       grind)
    | exact superpose eq63042 eq128
    | exact resolve eq128 eq63042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63042
  have eq65028 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25699 eq64974
    | exact resolve eq64974 eq25699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64974
  have eq65206 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X1)) X0) y)) = X2 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 X0 X1 X2 y y
       have i₂ := eq64924
       grind)
    | exact superpose eq64924 eq554
    | exact resolve eq554 eq64924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq64924
  have eq65446 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X2 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X1 X2
    first
    | (have i₁ := eq65206 x X1 X2
       have i₂ := eq2833 y x (M.op (M.op X1 X2) X1)
       grind)
    | exact superpose eq2833 eq65206
    | exact resolve eq65206 eq2833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2833 eq65206
  have eq98453 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63546 eq64981
    | exact resolve eq64981 eq63546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63546 eq64981
  have eq98510 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq98453
  have eq98514 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98510
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq98510
    | exact resolve eq98510 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98510
  have eq99274 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65028
       have i₂ := eq62939
       grind)
    | exact superpose eq62939 eq65028
    | exact resolve eq65028 eq62939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62939 eq65028
  have eq99331 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq99274
  have eq99334 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq99331
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq99331
    | exact resolve eq99331 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99331
  have eq99343 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq99334 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq99334
       grind)
    | exact resolve eq13 eq99334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99334
  have eq99454 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq99343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99343
  have eq100253 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq99454 eq98514
    | exact resolve eq98514 eq99454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98514 eq99454
  have eq100291 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq100253
  have eq100412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq100291 eq65446
    | exact resolve eq65446 eq100291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65446 eq100291
  have eq100413 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq100412
  have eq100415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq100413
    | exact resolve eq100413 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100413
  have eq100445 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq100415
       have r₂ := eq27
       grind)
    | exact resolve eq100415 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100415
  have eq100448 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100445 eq27
    | exact resolve eq27 eq100445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100450 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100445 eq73
    | (have r₁ := eq73
       have r₂ := eq100445
       grind)
    | exact resolve eq73 eq100445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq100445
  have eq100538 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq100450
  have eq158062 : (τ (σ y)) = (k y y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100538 eq25707
    | exact resolve eq25707 eq100538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25707 eq100538
  have eq158223 : (σ x) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq158062
    | exact resolve eq158062 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq158062
  have eq158430 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq158223 eq112
    | exact resolve eq112 eq158223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq158223
  have eq158451 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) := by grind
  clear eq158430
  have eq158462 : x = (M.op x y) ∨ y = (M.op y y) ∨ y = (k y y) := by
    first
    | (have r₁ := eq158451
       have r₂ := eq100448
       grind)
    | exact resolve eq158451 eq100448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100448 eq158451
  have eq158468 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq8889 y
       grind)
    | (have r₁ := eq158462
       have r₂ := eq8889 y
       grind)
    | exact resolve eq158462 eq8889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889 eq158462
  have eq158476 : x = (M.op (M.op y y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1279 y
       have i₂ := eq158468
       grind)
    | exact superpose eq158468 eq1279
    | exact resolve eq1279 eq158468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158483 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq158468
       grind)
    | exact superpose eq158468 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq158468
       grind)
    | exact resolve eq13 eq158468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158600 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq158483 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158483
  have eq158646 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq158476
       have i₂ := eq158468
       grind)
    | exact superpose eq158468 eq158476
    | exact resolve eq158476 eq158468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158476
  have eq158789 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq158646
  have eq158979 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op (M.op x y) x)) X0))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq158789 eq572
    | exact resolve eq572 eq158789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq159052 : ∀ X0 X2 X3 : G, (M.op (M.op X3 X2) X3) = (M.op y (M.op X0 (M.op (M.op X2 y) X0))) ∨ x = (M.op x y) := by
    intro X0 X2 X3
    first
    | exact superpose eq9002 eq158979
    | exact resolve eq158979 eq9002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9002 eq158979
  have eq159126 : ∀ X2 X3 : G, (M.op (M.op X3 X2) X3) = X2 ∨ x = (M.op x y) := by
    intro X2 X3
    first
    | (have i₁ := eq159052 x X2 X3
       have i₂ := eq503 X2 y x
       grind)
    | exact superpose eq503 eq159052
    | exact resolve eq159052 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq159052
  have eq163182 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq158600 y
       grind)
    | exact superpose eq158600 eq70
    | exact resolve eq70 eq158600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq163192 : (σ (M.op y (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq158600 sF0
       grind)
    | exact superpose eq158600 eq128
    | exact resolve eq128 eq158600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq158600
  have eq163246 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25699 eq163182
    | exact resolve eq163182 eq25699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25699 eq163182
  have eq210455 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) ∨ y = (M.op y y) ∨ (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) = (k (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) y) := by
    intro X0
    first
    | exact superpose eq1179 eq790
    | (have j0 := eq790 X0 y x
       grind)
    | exact resolve eq790 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq1179
  have eq210736 : ∀ X0 : G, x ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) = (k (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) y) := by
    intro X0
    first
    | exact superpose eq870 eq210455
    | (have j0 := eq210455 X0
       grind)
    | exact resolve eq210455 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210455
  have eq210926 : ∀ X0 : G, y = (M.op y y) ∨ (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) = (k (M.op (M.op (M.op X0 x) X0) (M.op x (M.op y (M.op x y)))) y) := by
    intro X0
    first
    | (have j0 := eq210736 X0
       grind)
    | (have r₁ := eq210736 X0
       have r₂ := eq158468
       grind)
    | exact resolve eq210736 eq158468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210736
  have eq210965 : y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq870 eq210926
    | exact resolve eq210926 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq210926
  have eq210984 : x = (M.op (M.op y y) (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1279 y
       have i₂ := eq210965
       grind)
    | exact superpose eq210965 eq1279
    | exact resolve eq1279 eq210965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq210992 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq210965
       grind)
    | exact superpose eq210965 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq210965
       grind)
    | exact resolve eq13 eq210965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211127 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ x = (k x y) := by
    intro X0
    first
    | (have j0 := eq210992 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210992
  have eq319344 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq158789 eq163192
    | exact resolve eq163192 eq158789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158789 eq163192
  have eq319421 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq319344
  have eq319425 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq319421
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq319421
    | exact resolve eq319421 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319421
  have eq319537 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq163246
       have i₂ := eq158468
       grind)
    | exact superpose eq158468 eq163246
    | exact resolve eq163246 eq158468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158468 eq163246
  have eq319614 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq319537
  have eq319619 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq319614
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq319614
    | exact resolve eq319614 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319614
  have eq319637 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq319619 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq319619
       grind)
    | exact resolve eq13 eq319619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319619
  have eq319812 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq319637 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319637
  have eq321211 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq319812 eq319425
    | exact resolve eq319425 eq319812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319425 eq319812
  have eq321262 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq321211
  have eq321460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq321262 eq159126
    | exact resolve eq159126 eq321262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159126 eq321262
  have eq321461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq321460
  have eq321468 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq321461
    | exact resolve eq321461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321461
  have eq321559 : x = (M.op x y) := by
    first
    | (have r₁ := eq321468
       have r₂ := eq27
       grind)
    | exact resolve eq321468 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321468
  have eq321581 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq321559 eq20
    | exact resolve eq20 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq321849 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq321581
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq321581
    | exact resolve eq321581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321581
  have eq321872 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq321849 eq26
    | exact resolve eq26 eq321849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405913 : x = (M.op (M.op y y) x) ∨ x = (k x y) := by
    first
    | exact superpose eq321559 eq210984
    | exact resolve eq210984 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210984
  have eq405997 : x ≠ (M.op y x) ∨ x = (k x y) := by grind
  clear eq211127
  have eq410651 : x = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq405913
       have i₂ := eq210965
       grind)
    | exact superpose eq210965 eq405913
    | exact resolve eq405913 eq210965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210965 eq405913
  have eq410890 : x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq410651
  have eq411042 : x = (k x y) := by
    first
    | (have r₁ := eq410890
       have r₂ := eq405997
       grind)
    | exact resolve eq410890 eq405997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405997 eq410890
  have eq411175 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq411042
       grind)
    | exact superpose eq411042 eq44
    | exact resolve eq44 eq411042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq411192 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq686 x y
       have i₂ := eq411042
       grind)
    | exact superpose eq411042 eq686
    | (have j0 := eq686 x y
       grind)
    | exact resolve eq686 eq411042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq411042
  have eq411194 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq411192
  have eq411198 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq411194
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq411194
    | exact resolve eq411194 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411194
  have eq411213 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq321849 eq411175
    | exact resolve eq411175 eq321849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411175
  have eq411216 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq411198
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq411198
    | exact resolve eq411198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411198
  have eq411230 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq411213
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq411213
    | exact resolve eq411213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq411213
  have eq411232 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq411216
    | exact resolve eq411216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq411216
  have eq411245 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq321849 eq411230
    | exact resolve eq411230 eq321849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411230
  have eq411247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq321849 eq411232
    | exact resolve eq411232 eq321849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411232
  have eq411257 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq411247
       have r₂ := eq27
       grind)
    | exact resolve eq411247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411247
  have eq411264 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq411257
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq411257
    | exact resolve eq411257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq411257
  have eq413955 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq411264 eq1285
    | exact resolve eq1285 eq411264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq413965 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | exact superpose eq411264 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq411264
       grind)
    | exact resolve eq13 eq411264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414150 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq413965 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413965
  have eq414310 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq411264 eq413955
    | exact resolve eq413955 eq411264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411264 eq413955
  have eq414431 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq321849 eq414310
    | exact resolve eq414310 eq321849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414310
  have eq416385 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 x)) = (M.op X1 (M.op X2 (M.op (M.op X0 (M.op y x)) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq321559 eq1206
    | exact resolve eq1206 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq417706 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op (M.op X0 (M.op y x)) X1)) (M.op (σ x) (M.op (M.op (M.op y (M.op x y)) (M.op X0 x)) (M.op (σ y) (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq12107 (M.op x (M.op (M.op X0 (M.op y x)) x))
       have i₂ := eq416385 X0 (M.op y sF0) x
       grind)
    | exact superpose eq416385 eq12107
    | exact resolve eq12107 eq416385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12107 eq416385
  have eq417929 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op (M.op X0 (M.op y x)) X1)) (M.op (σ x) (M.op (M.op (M.op y (M.op x y)) (M.op X0 x)) (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq414431 eq417706
    | exact resolve eq417706 eq414431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414431 eq417706
  have eq418692 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op (M.op X0 (M.op y x)) X1)) (M.op (σ x) (M.op X0 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq816 eq417929
    | exact resolve eq417929 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq417929
  have eq419032 : ∀ X0 X1 : G, x = (M.op (M.op X1 (M.op (M.op X0 (M.op y x)) X1)) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq321849 eq418692
    | exact resolve eq418692 eq321849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321849 eq418692
  have eq419172 : x = (M.op y x) := by
    first
    | (have i₁ := eq419032 x x
       have i₂ := eq799 x x (M.op y x) sF1
       grind)
    | exact superpose eq799 eq419032
    | exact resolve eq419032 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq419032
  have eq421241 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op y x))) X1) (M.op X2 (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq321559 eq1207
    | exact resolve eq1207 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq421242 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X0 x)) X1) (M.op X2 (M.op X0 x))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq421241 X0 X1 X2
       have i₂ := eq419172
       grind)
    | exact superpose eq419172 eq421241
    | exact resolve eq421241 eq419172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421241
  have eq421243 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op y (M.op x y))) (M.op X2 (M.op X0 x))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq421242 X0 x X2
       have i₂ := eq209 x X0
       grind)
    | exact superpose eq209 eq421242
    | exact resolve eq421242 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq421242
  have eq421244 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op y x)) (M.op X2 (M.op X0 x))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq321559 eq421243
    | exact resolve eq421243 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421243
  have eq421245 : ∀ X0 X2 : G, (M.op (M.op X0 x) (M.op X2 (M.op X0 x))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq421244 X0 X2
       have i₂ := eq419172
       grind)
    | exact superpose eq419172 eq421244
    | exact resolve eq421244 eq419172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421244
  have eq421246 : ∀ X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (σ x) (σ y)))) = X2 := by
    intro X2
    first
    | (have i₁ := eq421245 x X2
       have i₂ := eq2909 X2 (M.op x x)
       grind)
    | exact superpose eq2909 eq421245
    | exact resolve eq421245 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421245
  have eq421247 : ∀ X2 : G, (M.op (M.op x y) (M.op X2 (M.op x y))) = X2 := by
    intro X2
    first
    | (have i₁ := eq421246 x
       have i₂ := eq3015 x sF4
       grind)
    | exact superpose eq3015 eq421246
    | exact resolve eq421246 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421246
  have eq421248 : ∀ X2 : G, (M.op x (M.op X2 x)) = X2 := by
    intro X2
    first
    | exact superpose eq321559 eq421247
    | exact resolve eq421247 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421247
  have eq422698 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op y x)) (M.op (M.op X1 X2) (M.op X0 x))) X1) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq321559 eq1208
    | exact resolve eq1208 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq422699 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) (M.op (M.op X1 X2) (M.op X0 x))) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq422698 X0 X1 X2
       have i₂ := eq419172
       grind)
    | exact superpose eq419172 eq422698
    | exact resolve eq422698 eq419172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419172 eq422698
  have eq422700 : ∀ X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X2) (M.op (σ x) (σ y)))) X1) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq422699 x X1 X2
       have i₂ := eq2909 (M.op X1 X2) (M.op x x)
       grind)
    | exact superpose eq2909 eq422699
    | exact resolve eq422699 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909 eq422699
  have eq422701 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) (M.op (M.op X1 X2) (M.op x y))) X1) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq422700 X1 X2
       have i₂ := eq3015 (M.op X1 X2) sF4
       grind)
    | exact superpose eq3015 eq422700
    | exact resolve eq422700 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015 eq422700
  have eq422702 : ∀ X1 X2 : G, (M.op (M.op x (M.op (M.op X1 X2) x)) X1) = X2 := by
    intro X1 X2
    first
    | exact superpose eq321559 eq422701
    | exact resolve eq422701 eq321559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321559 eq422701
  have eq422703 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq422702 X1 X2
       have i₂ := eq421248 (M.op X1 X2)
       grind)
    | (have i₁ := eq422702 X1 X2
       have i₂ := eq421248 (M.op x (M.op (M.op X1 X2) x))
       grind)
    | exact superpose eq421248 eq422702
    | exact resolve eq422702 eq421248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421248 eq422702
  have eq436733 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq411245 eq414150
    | exact resolve eq414150 eq411245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411245 eq414150
  have eq437106 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq436733 eq422703
    | exact resolve eq422703 eq436733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422703 eq436733
  have eq437109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq321872 eq437106
    | exact resolve eq437106 eq321872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321872 eq437106
  have eq437286 : False := by grind
  exact eq437286

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ y = (k y x) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq27
    | exact resolve eq27 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq378 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq125
  have eq379 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq378
  have eq382 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq379 eq116
    | exact resolve eq116 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq386 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq382
  have eq391 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq386
       have r₂ := eq127
       grind)
    | exact resolve eq386 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq386
  have eq395 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq391 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq391
       grind)
    | exact resolve eq13 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq401 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq395 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq503 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq401 eq116
    | exact resolve eq116 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq401
  have eq506 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq503
  have eq511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq506
    | exact resolve eq506 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq513 : y = (M.op x y) := by
    first
    | (have r₁ := eq511
       have r₂ := eq27
       grind)
    | exact resolve eq511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq515 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq513 eq20
    | exact resolve eq20 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq519 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq513 eq72
    | (have r₁ := eq72
       have r₂ := eq513
       grind)
    | exact resolve eq72 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq523 : y = (k y x) ∨ x = (M.op x x) := by grind
  clear eq519
  have eq529 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq515
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq515
    | exact resolve eq515 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq585 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq529 eq26
    | exact resolve eq26 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq651 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq94
    | (have j0 := eq94 (M.op x y) X0
       grind)
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq664 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq513 eq651
    | (have j0 := eq651 X0
       grind)
    | exact resolve eq651 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq897 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq523
       grind)
    | exact superpose eq523 eq69
    | exact resolve eq69 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq904 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq529 eq897
    | exact resolve eq897 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq906 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq904
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq904
    | exact resolve eq904 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq904
  have eq907 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq529 eq906
    | exact resolve eq906 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq912 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq907 eq90
    | (have j0 := eq90 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq90 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq907
  have eq913 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by grind
  clear eq912
  have eq915 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq585 eq913
    | exact resolve eq913 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq918 : x = (M.op x x) := by
    first
    | (have r₁ := eq915
       have r₂ := eq27
       grind)
    | exact resolve eq915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq922 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq918
       grind)
    | exact resolve eq13 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq931 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq922 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq949 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq664 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq664
    | (have j0 := eq664 x
       grind)
    | exact resolve eq664 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq664
  have eq965 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq585 eq949
    | exact resolve eq949 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq978 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq965
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq965
    | exact resolve eq965 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq965
  have eq987 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq529 eq978
    | exact resolve eq978 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq978
  have eq992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq585 eq987
    | exact resolve eq987 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585 eq987
  have eq993 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq992
       have r₂ := eq27
       grind)
    | exact resolve eq992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1025 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq135
       have i₂ := eq931 sF0
       grind)
    | exact superpose eq931 eq135
    | exact resolve eq135 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq931
  have eq1028 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq513 eq1025
    | exact resolve eq1025 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq1025
  have eq1033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq993 eq1028
    | exact resolve eq1028 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993 eq1028
  have eq1038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1033
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1033
    | exact resolve eq1033 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1033
  have eq1040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1038
    | exact resolve eq1038 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1038
  have eq1042 : False := by grind
  exact eq1042

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation2373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X0 X3))) = (M.op (M.op X1 (M.op X2 X0)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X3 (M.op X0 X3))) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq14 X0 (M.op X1 (M.op X2 X1)) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq72 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq73 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq27
    | exact resolve eq27 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq125
  have eq367 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq366
  have eq370 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq367 eq116
    | exact resolve eq116 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq374 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq370
  have eq379 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq374
       have r₂ := eq127
       grind)
    | exact resolve eq374 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq374
  have eq383 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq379 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq379
       grind)
    | exact resolve eq13 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq387 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq383 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq486 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq387 eq116
    | exact resolve eq116 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq387
  have eq489 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq486
  have eq494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq489
    | exact resolve eq489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq496 : x = (M.op x y) := by
    first
    | (have r₁ := eq494
       have r₂ := eq27
       grind)
    | exact resolve eq494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq498 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq496 eq20
    | exact resolve eq20 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 : G, x = (M.op (M.op X0 (M.op y x)) X0) := by
    intro X0
    first
    | exact superpose eq496 eq50
    | exact resolve eq50 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq502 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq496 eq72
    | (have r₁ := eq72
       have r₂ := eq496
       grind)
    | exact resolve eq72 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq506 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq502
  have eq512 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq498
    | exact resolve eq498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq541 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op y (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq563 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 (M.op X1 X0)) (M.op y x))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq496 eq541
    | exact resolve eq541 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq567 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq512 eq26
    | exact resolve eq26 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq620 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq94
    | (have j0 := eq94 X0 (M.op x y)
       grind)
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq658 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq496 eq620
    | (have j0 := eq620 X0
       grind)
    | exact resolve eq620 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq620
  have eq736 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq500 x
       have i₂ := eq52 x x y X0
       grind)
    | exact superpose eq52 eq500
    | exact resolve eq500 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq500
  have eq841 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq506
       grind)
    | exact superpose eq506 eq69
    | exact resolve eq69 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq848 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq512 eq841
    | exact resolve eq841 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq850 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq848
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq848
    | exact resolve eq848 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq851 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq512 eq850
    | exact resolve eq850 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq854 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq851 eq90
    | (have j0 := eq90 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq90 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq851
  have eq855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq854
  have eq857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq567 eq855
    | exact resolve eq855 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq860 : x = (M.op x x) := by
    first
    | (have r₁ := eq857
       have r₂ := eq27
       grind)
    | exact resolve eq857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq913 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq736 x
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq736
    | exact resolve eq736 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq914 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq860
       grind)
    | exact resolve eq13 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq930 : x = (M.op y x) := by
    first
    | (have i₁ := eq913
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq913
    | exact resolve eq913 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq944 : y = (M.op x (M.op (M.op x x) x)) := by
    first
    | (have i₁ := eq563 x y
       have i₂ := eq930
       grind)
    | exact superpose eq930 eq563
    | exact resolve eq563 eq930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq930
  have eq946 : y = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq944
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq944
    | exact resolve eq944 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq952 : y = (M.op x x) := by
    first
    | (have i₁ := eq946
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq946
    | exact resolve eq946 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq954 : x = y := by
    first
    | (have i₁ := eq952
       have i₂ := eq860
       grind)
    | exact superpose eq860 eq952
    | exact resolve eq952 eq860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860 eq952
  have eq969 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq658 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq658
    | (have j0 := eq658 y
       grind)
    | exact resolve eq658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq986 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq567 eq969
    | exact resolve eq969 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq999 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq986
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq986
    | exact resolve eq986 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1008 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq512 eq999
    | exact resolve eq999 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq567 eq1008
    | exact resolve eq1008 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1008
  have eq1015 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1013
       have r₂ := eq27
       grind)
    | exact resolve eq1013 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1017 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq954
       grind)
    | exact superpose eq954 eq24
    | exact resolve eq24 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq954
  have eq1044 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1017
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1017
    | exact resolve eq1017 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1017
  have eq1052 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq512 eq1044
    | exact resolve eq1044 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1095 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1052 eq1015
    | exact resolve eq1015 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1217 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq923 y
       grind)
    | exact superpose eq923 eq69
    | exact resolve eq69 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq923
  have eq1222 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq512 eq1217
    | exact resolve eq1217 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq1217
  have eq1228 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1052 eq1222
    | exact resolve eq1222 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1222
  have eq1231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1095 eq1228
    | exact resolve eq1228 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq1228
  have eq1234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1231
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1231
    | exact resolve eq1231 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1231
  have eq1237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1234
    | exact resolve eq1234 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1234
  have eq1240 : False := by grind
  exact eq1240

/-- `Equation2373`: `x = (y ◇ (z ◇ (x ◇ z))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2373 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2373 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2373.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq62447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq62447
    | exact resolve eq62447 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62447
  have eq62459 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq62448
       have r₂ := eq28
       grind)
    | exact resolve eq62448 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62448
  have eq62463 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq62459
    | exact resolve eq62459 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62459
  have eq62476 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq62463 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq62463
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq62463
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq62463
       grind)
    | exact resolve eq12 eq62463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62463
  have eq62576 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq62476
  have eq62605 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq62576
       have r₂ := eq27
       grind)
    | exact resolve eq62576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62576
  have eq63451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq62605 eq104
    | exact resolve eq104 eq62605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq62605
  have eq63460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq63451
  have eq63463 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq63460
       have r₂ := eq28
       grind)
    | exact resolve eq63460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63460
  have eq63476 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq63463
       grind)
    | exact superpose eq63463 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq63463
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq63463
       grind)
    | exact resolve eq12 eq63463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63463
  have eq63576 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq63476
  have eq63605 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq63576
       have r₂ := eq19
       grind)
    | exact resolve eq63576 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63576
  have eq64589 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq63605
       grind)
    | exact superpose eq63605 eq89
    | exact resolve eq89 eq63605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq63605
  have eq64605 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq64589
    | exact resolve eq64589 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64589
  have eq64640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq64605 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq64605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq64640
  have eq64645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq64641
    | exact resolve eq64641 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64641
  have eq64656 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq64645
       have r₂ := eq28
       grind)
    | exact resolve eq64645 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64645
  have eq64660 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq64656
    | exact resolve eq64656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64656
  have eq65690 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq64660 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq64660
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq64660
       grind)
    | exact resolve eq12 eq64660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64660
  have eq65794 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq65690
  have eq65823 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq65794
       have r₂ := eq27
       grind)
    | exact resolve eq65794 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65794
  have eq66320 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq65823 eq64605
    | exact resolve eq64605 eq65823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64605 eq65823
  have eq66323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq66320
  have eq66328 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq66323
       have r₂ := eq28
       grind)
    | exact resolve eq66323 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66323
  have eq66331 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq66328 eq30
    | exact resolve eq30 eq66328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq66328
  have eq66500 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq66331
    | exact resolve eq66331 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq66331
  have eq66501 : x = y := by grind
  clear eq66500
  have eq66520 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq66501
       grind)
    | exact superpose eq66501 eq19
    | exact resolve eq19 eq66501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq66521 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq66501
       grind)
    | exact superpose eq66501 eq25
    | exact resolve eq25 eq66501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq66501
  have eq66688 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq66521
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq66521
    | exact resolve eq66521 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq66521
  have eq67418 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq66688 eq27
    | exact resolve eq27 eq66688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq66688
  have eq67962 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq67418 eq68
    | exact resolve eq68 eq67418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq67418
  have eq68162 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq67962
       have i₂ := eq66520
       grind)
    | exact superpose eq66520 eq67962
    | exact resolve eq67962 eq66520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66520 eq67962
  have eq68264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68162 eq15
    | exact resolve eq15 eq68162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68162
  have eq68310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq68264
    | exact resolve eq68264 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68264
  have eq68319 : False := by grind
  exact eq68319

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
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
  have eq30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq44 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq52 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq43 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq110 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq356 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq357 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq362 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       have j1 := eq110 X0 X1
       grind)
    | (have r₁ := eq357 X0 X1
       have r₂ := eq110 X0 X1
       grind)
    | (have r₁ := eq357 X1 X1
       have r₂ := eq110 X1 X1
       grind)
    | exact resolve eq357 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq357
  have eq564 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq362 (σ X1) (σ X0)
       grind)
    | exact superpose eq362 eq15
    | exact resolve eq15 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq564 X0 X1
       have i₂ := eq362 X1 X0
       grind)
    | exact superpose eq362 eq564
    | exact resolve eq564 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq564
  have eq574 : False := by grind
  exact eq574

/-- `Equation2452`: `x = (x ◇ ((x ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq47 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq50
    | exact resolve eq50 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq50
  have eq80 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq80
    | (have j0 := eq80 X0 X1
       grind)
    | exact resolve eq80 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq94 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq234 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq246 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq234 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq253 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq246 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq246 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq246 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq264 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq253 X0 X1
       have j1 := eq94 X0 (σ X1)
       grind)
    | (have r₁ := eq253 X0 X1
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq253 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq253
  have eq272 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq264 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq264
    | (have j0 := eq264 X0 X1
       grind)
    | exact resolve eq264 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq277 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq273 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273
    | exact resolve eq273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq273 x y
       grind)
    | exact superpose eq273 eq16
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq433 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq277 X0 (τ X1)
       grind)
    | exact superpose eq277 eq17
    | exact resolve eq17 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq277
  have eq449 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq433 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq433
    | exact resolve eq433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq457 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq449
    | exact resolve eq449 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq472 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq289
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq289
    | exact resolve eq289 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq457
  have eq473 : False := by grind
  exact eq473

/-- `Equation2503`: `x = (y ◇ ((x ◇ y) ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation2503 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2503 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2503.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq447 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq430 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq430
    | (have j0 := eq430 X0 X1
       grind)
    | exact resolve eq430 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq732 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq447 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq447
    | exact resolve eq447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq746 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq732 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq732
    | (have j0 := eq732 X0 X1
       grind)
    | exact resolve eq732 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq732
  have eq754 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq746 X0 X1
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq746 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq746 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq746 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq746
  have eq757 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq754 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq754
    | exact resolve eq754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq754 (σ X1) X0
       grind)
    | exact superpose eq754 eq15
    | (have j1 := eq754 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq807 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq757 (τ X0) X1
       grind)
    | exact superpose eq757 eq19
    | (have j1 := eq757 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq757
  have eq907 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq807 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq807
    | exact resolve eq807 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq948 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq907 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq907
    | (have j0 := eq907 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq907 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1133 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq772 x y
       grind)
    | exact superpose eq772 eq16
    | (have j1 := eq772 x y
       grind)
    | exact resolve eq16 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1133
       have i₂ := eq948 x y
       grind)
    | exact superpose eq948 eq1133
    | (have j1 := eq948 (σ x) (σ y)
       grind)
    | (have r₁ := eq1133
       have r₂ := eq948 x y
       grind)
    | (have r₁ := eq1133
       have r₂ := eq948 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1133
       have r₂ := eq948 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1133 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948 eq1133
  have eq1150 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1149
  have eq1153 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1150
       grind)
    | exact superpose eq1150 eq16
    | exact resolve eq16 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1154 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1153
       have r₂ := eq79 x
       grind)
    | exact resolve eq1153 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153
  have eq1155 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq16
    | exact resolve eq16 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1154
       grind)
    | exact superpose eq1154 eq10
    | exact resolve eq10 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq1201 : x = y := by
    first
    | (have i₁ := eq1156
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1156
    | exact resolve eq1156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1202 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq1155
    | exact resolve eq1155 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1155
  have eq1203 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1202
       have i₂ := eq1201
       grind)
    | exact superpose eq1201 eq1202
    | exact resolve eq1202 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq1202
  have eq1204 : False := by grind
  exact eq1204
