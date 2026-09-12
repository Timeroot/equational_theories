import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_x_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq47 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) X0) x) X0) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 X0) ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq83 : (k x x) = (τ (k (σ x) (σ x))) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq95
    | exact resolve eq95 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq102 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq166 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq143 eq16
    | exact resolve eq16 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq672 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) (σ X1)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq51
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq51 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq839 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (M.op (M.op (M.op X1 X2) x) X1) x x
       have i₂ := eq49 x X1 X2 x
       grind)
    | exact superpose eq49 eq71
    | exact resolve eq71 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq71
  have eq873 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x X0 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq9158 : (σ x) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq672 x y
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq672
    | (have j0 := eq672 x y
       grind)
    | exact resolve eq672 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq672
  have eq9354 : (σ x) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9158
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9158
    | exact resolve eq9158 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9158
  have eq9446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9354
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9354
    | exact resolve eq9354 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9354
  have eq9533 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9446
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9446
    | exact resolve eq9446 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9446
  have eq9618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq9533
    | exact resolve eq9533 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9533
  have eq9702 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq9618
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9618
    | exact resolve eq9618 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9618
  have eq9757 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq9702
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9702
    | exact resolve eq9702 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9702
  have eq10634 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    grind
  clear eq839
  have eq10668 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq10634 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10634
  have eq10766 : x = (k x (M.op x y)) := by
    first
    | exact superpose eq47 eq10668
    | exact resolve eq10668 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq10769 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq48 eq10668
    | exact resolve eq10668 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq10668
  have eq10811 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq10766 eq46
    | exact resolve eq46 eq10766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq10829 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10811
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10811
    | exact resolve eq10811 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10811
  have eq18208 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18208
    | exact resolve eq18208 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18208
  have eq18227 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18216
       have r₂ := eq28
       grind)
    | exact resolve eq18216 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18216
  have eq18231 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18227
    | exact resolve eq18227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18227
  have eq18240 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18231 eq51
    | exact resolve eq51 eq18231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18231
  have eq18283 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18240
    | exact resolve eq18240 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18240
  have eq18284 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18283
  have eq18292 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq18284
       grind)
    | exact superpose eq18284 eq51
    | exact resolve eq51 eq18284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18284
  have eq18335 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18292
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18292
    | exact resolve eq18292 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292
  have eq18336 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18335
  have eq18364 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18336 eq10769
    | exact resolve eq10769 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10769 eq18336
  have eq18427 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18364 eq97
    | exact resolve eq97 eq18364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq18364
  have eq18441 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq18427
  have eq19459 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq51 y y
       have i₂ := eq18441
       grind)
    | exact superpose eq18441 eq51
    | exact resolve eq51 eq18441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18441
  have eq19502 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq19459
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19459
    | exact resolve eq19459 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19459
  have eq19503 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq19502
  have eq19517 : (k x x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19503 eq83
    | exact resolve eq83 eq19503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq19523 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19503 eq102
    | exact resolve eq102 eq19503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq19503
  have eq19641 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166 eq19523
    | exact resolve eq19523 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19523
  have eq19643 : (k x x) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166 eq19517
    | exact resolve eq19517 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq19517
  have eq19660 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10766 eq19641
    | exact resolve eq19641 eq10766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10766 eq19641
  have eq26196 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19643 eq19660
    | exact resolve eq19660 eq19643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19643 eq19660
  have eq26221 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq26196
  have eq26273 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq26221
       grind)
    | exact superpose eq26221 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq26221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26221
  have eq26287 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq26273
  have eq26589 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq873 x
       have i₂ := eq26287
       grind)
    | exact superpose eq26287 eq873
    | exact resolve eq873 eq26287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq26287
  have eq26660 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52 eq26589
    | exact resolve eq26589 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq26589
  have eq26668 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq26660
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26660
    | exact resolve eq26660 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq26660
  have eq26669 : y = (M.op x y) := by grind
  clear eq26668
  have eq26675 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26669 eq21
    | exact resolve eq21 eq26669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq26669
  have eq26815 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26675
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26675
    | exact resolve eq26675 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq26675
  have eq26834 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq26815 eq27
    | exact resolve eq27 eq26815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40765 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26815 eq9757
    | exact resolve eq9757 eq26815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757
  have eq40766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26815 eq40765
    | exact resolve eq40765 eq26815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40765
  have eq40767 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ x) (σ y)) (σ x)) := by
    first
    | (have r₁ := eq40766
       have r₂ := eq28
       grind)
    | exact resolve eq40766 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40766
  have eq40768 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26815 eq40767
    | exact resolve eq40767 eq26815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40767
  have eq40769 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq10829 eq40768
    | exact resolve eq40768 eq10829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10829 eq40768
  have eq40778 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq40769 eq877
    | exact resolve eq877 eq40769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq40769
  have eq40865 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26815 eq40778
    | exact resolve eq40778 eq26815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26815 eq40778
  have eq40877 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq53 eq40865
    | exact resolve eq40865 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq40865
  have eq40881 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26834 eq40877
    | exact resolve eq40877 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40877
  have eq40884 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq40881
       have r₂ := eq28
       grind)
    | exact resolve eq40881 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40881
  have eq40902 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq40884 eq51
    | exact resolve eq51 eq40884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq40884
  have eq40958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26834 eq40902
    | exact resolve eq40902 eq26834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26834 eq40902
  have eq40960 : False := by grind
  exact eq40960

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
    intro X0 X1 X2
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 X0) ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (k (M.op (M.op (M.op X1 X2) X0) X1) X0) ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq108 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq119
    | exact resolve eq119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq672 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq51
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq51 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq838 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (M.op (M.op (M.op X1 X2) x) X1) x x
       have i₂ := eq49 x X1 X2 x
       grind)
    | exact superpose eq49 eq71
    | exact resolve eq71 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq71
  have eq9407 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    grind
  clear eq838
  have eq9441 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq9407 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9407
  have eq9544 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq61 eq9441
    | exact resolve eq9441 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq9546 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9441 (M.op X0 X1) X0 X0
       have i₂ := eq57 X0 X1 X0
       grind)
    | exact superpose eq57 eq9441
    | exact resolve eq9441 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq9441
  have eq37737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq37737
    | exact resolve eq37737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37737
  have eq37755 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq37744
       have r₂ := eq28
       grind)
    | exact resolve eq37744 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37744
  have eq37788 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq37755 eq51
    | exact resolve eq51 eq37755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37755
  have eq37843 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq37788
  have eq37864 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq37843 eq51
    | exact resolve eq51 eq37843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37843
  have eq37921 : y = (M.op x x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq37864
    | exact resolve eq37864 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37864
  have eq37947 : x = (M.op y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq51 x x
       have i₂ := eq37921
       grind)
    | exact superpose eq37921 eq51
    | exact resolve eq51 eq37921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37921
  have eq38002 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37947
  have eq38475 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9546 y x
       have i₂ := eq38002
       grind)
    | exact superpose eq38002 eq9546
    | exact resolve eq9546 eq38002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9546 eq38002
  have eq39039 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq672 x y
       have i₂ := eq38475
       grind)
    | exact superpose eq38475 eq672
    | (have j0 := eq672 x y
       grind)
    | exact resolve eq672 eq38475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq38475
  have eq39044 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39039
  have eq39048 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39044
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39044
    | exact resolve eq39044 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39044
  have eq39062 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39048
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39048
    | exact resolve eq39048 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39048
  have eq39069 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq39062
    | exact resolve eq39062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39062
  have eq39070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq39069
  have eq39075 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39070
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39070
    | exact resolve eq39070 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39070
  have eq39081 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39075
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39075
    | exact resolve eq39075 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq39075
  have eq39625 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39081 eq51
    | exact resolve eq51 eq39081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39081
  have eq39682 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq39625
    | exact resolve eq39625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq39625
  have eq39683 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq39682
  have eq39685 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq39683 eq28
    | exact resolve eq28 eq39683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39727 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq39683 eq9544
    | exact resolve eq9544 eq39683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544 eq39683
  have eq39861 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq39727 eq120
    | exact resolve eq120 eq39727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq39727
  have eq39883 : y = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq39861
       have r₂ := eq39685
       grind)
    | exact resolve eq39861 eq39685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39861
  have eq42431 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq51 x x
       have i₂ := eq39883
       grind)
    | exact superpose eq39883 eq51
    | exact resolve eq51 eq39883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39883
  have eq42488 : x = (M.op y x) := by grind
  clear eq42431
  have eq42520 : y = (M.op x y) := by
    first
    | (have i₁ := eq51 y x
       have i₂ := eq42488
       grind)
    | exact superpose eq42488 eq51
    | exact resolve eq51 eq42488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq42488
  have eq42581 : y = (M.op x y) := by
    first
    | (have i₁ := eq42520
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq42520
    | exact resolve eq42520 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq42520
  have eq42582 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq42581 eq21
    | exact resolve eq21 eq42581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq42581
  have eq42772 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq42582
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq42582
    | exact resolve eq42582 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq42582
  have eq42791 : False := by grind
  exact eq42791

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107
    | exact resolve eq107 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq113
    | exact resolve eq113 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq114
    | exact resolve eq114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
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
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq377 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq63 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq63
    | (have j0 := eq63 y
       grind)
    | exact resolve eq63 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq420 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq95
    | (have j0 := eq95 (σ X0)
       grind)
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq44
    | (have j1 := eq95 x
       grind)
    | exact resolve eq44 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq427 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq173
       have i₂ := eq95 sF1
       grind)
    | exact superpose eq95 eq173
    | (have j1 := eq95 (σ (M.op x y))
       grind)
    | exact resolve eq173 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq480 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X0)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq832 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq61
    | (have j0 := eq61 (σ x) X0 (σ y)
       grind)
    | exact resolve eq61 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1115 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x y) (M.op (M.op X0 x) (M.op X0 X1))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq480 (M.op X0 X1) X0
       have i₂ := eq55 X0 X1
       grind)
    | exact superpose eq55 eq480
    | exact resolve eq480 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq4605 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq55 (σ X0) (σ X0)
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq55
    | (have j1 := eq420 X0
       grind)
    | exact resolve eq55 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq14328 : y = (M.op (M.op (M.op x y) (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y)) y) := by
    first
    | exact superpose eq377 eq1115
    | exact resolve eq1115 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq1115
  have eq18465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18465
    | exact resolve eq18465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18465
  have eq18477 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18466
       have r₂ := eq28
       grind)
    | exact resolve eq18466 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18466
  have eq18479 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18477
    | exact resolve eq18477 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18477
  have eq18483 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18479 eq93
    | (have r₁ := eq93
       have r₂ := eq18479
       grind)
    | exact resolve eq93 eq18479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq18529 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq18479
  have eq18531 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq18483
  have eq19097 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18531
       have r₂ := eq18529
       grind)
    | exact resolve eq18531 eq18529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18529 eq18531
  have eq19103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq19097 eq115
    | exact resolve eq115 eq19097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19097
  have eq19112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq19103
  have eq19115 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq19112
       have r₂ := eq28
       grind)
    | exact resolve eq19112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19112
  have eq19130 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq19115
  have eq19171 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq27 eq19130
    | exact resolve eq19130 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19130
  have eq19627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq19171 eq115
    | exact resolve eq115 eq19171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq19171
  have eq19635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq19627
  have eq19637 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19635
       have r₂ := eq28
       grind)
    | exact resolve eq19635 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19635
  have eq19639 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq424
       have i₂ := eq19637
       grind)
    | exact superpose eq19637 eq424
    | exact resolve eq424 eq19637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq19641 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq19637
       grind)
    | exact superpose eq19637 eq91
    | (have r₁ := eq91
       have r₂ := eq19637
       grind)
    | exact resolve eq91 eq19637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq19687 : y ≠ (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq19637
  have eq19689 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq19641
  have eq19698 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq19639
    | exact resolve eq19639 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19639
  have eq20320 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq19689
       have r₂ := eq19687
       grind)
    | exact resolve eq19689 eq19687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19687 eq19689
  have eq20322 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq20320
       grind)
    | exact superpose eq20320 eq102
    | exact resolve eq102 eq20320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq20320
  have eq20342 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq20322
    | exact resolve eq20322 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20322
  have eq20357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20342 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq20342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20357
    | exact resolve eq20357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20357
  have eq20373 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq20362
       have r₂ := eq28
       grind)
    | exact resolve eq20362 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20362
  have eq20375 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq20373
    | exact resolve eq20373 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20373
  have eq20378 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq19698
       have i₂ := eq95 sF2
       grind)
    | exact superpose eq95 eq19698
    | (have j1 := eq95 (σ x)
       grind)
    | exact resolve eq19698 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq19698
  have eq21630 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  have eq49819 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20378 eq832
    | exact resolve eq832 eq20378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20378
  have eq49930 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57 eq49819
    | exact resolve eq49819 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49819
  have eq49935 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq49930
    | exact resolve eq49930 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49930
  have eq49938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20375 eq49935
    | exact resolve eq49935 eq20375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20375 eq49935
  have eq50031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq49938
  have eq50043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq50031
       have r₂ := eq21630
       grind)
    | exact resolve eq50031 eq21630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21630 eq50031
  have eq50045 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq50043
       have r₂ := eq28
       grind)
    | exact resolve eq50043 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50043
  have eq50385 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq50045
  have eq50462 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq50385
    | exact resolve eq50385 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50385
  have eq51877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50462 eq20342
    | exact resolve eq20342 eq50462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20342 eq50462
  have eq51917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq51877
  have eq51930 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51917
       have r₂ := eq28
       grind)
    | exact resolve eq51917 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51917
  have eq51952 : y ≠ y ∨ x = y ∨ y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq51930
       grind)
    | exact superpose eq51930 eq12
    | exact resolve eq12 eq51930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51958 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq51930
       grind)
    | exact superpose eq51930 eq59
    | exact resolve eq59 eq51930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51930
  have eq52010 : x = y ∨ y = (k x x) ∨ x = (M.op x y) := by grind
  clear eq51952
  have eq52017 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51958
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51958
    | exact resolve eq51958 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51958
  have eq52021 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52017 eq21
    | exact resolve eq21 eq52017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52211 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq52017
  have eq52295 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52021
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq52021
    | exact resolve eq52021 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52021
  have eq61364 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq52010
       have r₂ := eq52211
       grind)
    | exact resolve eq52010 eq52211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52010 eq52211
  have eq91854 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4605 x
       have i₂ := eq61364
       grind)
    | exact superpose eq61364 eq4605
    | (have j0 := eq4605 x
       grind)
    | exact resolve eq4605 eq61364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4605 eq61364
  have eq92207 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91854
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91854
    | exact resolve eq91854 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91854
  have eq92245 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92207
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq92207
    | exact resolve eq92207 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92207
  have eq92271 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92245
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq92245
    | exact resolve eq92245 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92245
  have eq118738 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92271 eq55
    | exact resolve eq55 eq92271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92271
  have eq118809 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq118738
    | exact resolve eq118738 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118738
  have eq118824 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118809 eq832
    | exact resolve eq832 eq118809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq118809
  have eq118953 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57 eq118824
    | exact resolve eq118824 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq118824
  have eq118959 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq118953
    | exact resolve eq118953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118953
  have eq118960 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq118959
  have eq118963 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq118960 eq28
    | exact resolve eq28 eq118960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118960
  have eq119038 : x = (M.op x y) := by
    first
    | (have r₁ := eq118963
       have r₂ := eq52295
       grind)
    | exact resolve eq118963 eq52295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52295 eq118963
  have eq119829 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq119038 eq21
    | exact resolve eq21 eq119038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq119832 : x = (M.op x x) := by
    first
    | exact superpose eq119038 eq56
    | exact resolve eq56 eq119038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq120009 : y = (M.op (M.op x (M.op (M.op (M.op x x) x) y)) y) := by
    first
    | exact superpose eq119038 eq14328
    | exact resolve eq14328 eq119038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14328
  have eq120070 : y = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq120009
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq120009
    | exact resolve eq120009 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq120009
  have eq120232 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq119829
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq119829
    | exact resolve eq119829 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119829
  have eq120233 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq120070
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq120070
    | exact resolve eq120070 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq120070
  have eq120234 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq120233
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq120233
    | exact resolve eq120233 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120233
  have eq120235 : y = (M.op x y) := by
    first
    | exact superpose eq119038 eq120234
    | exact resolve eq120234 eq119038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120234
  have eq120236 : y = (M.op x y) := by
    first
    | (have i₁ := eq120235
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq120235
    | exact resolve eq120235 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq120235
  have eq120237 : x = y := by
    first
    | exact superpose eq119038 eq120236
    | exact resolve eq120236 eq119038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120236
  have eq120238 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq120232 eq27
    | exact resolve eq27 eq120232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq120627 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq120237
       grind)
    | exact superpose eq120237 eq25
    | exact resolve eq25 eq120237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq120237
  have eq121083 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq120627
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq120627
    | exact resolve eq120627 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120627
  have eq121220 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq120232 eq121083
    | exact resolve eq121083 eq120232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121083
  have eq121709 : (k x x) = (M.op x x) := by grind
  have eq121813 : x = (k x x) := by
    first
    | (have i₁ := eq121709
       have i₂ := eq119832
       grind)
    | exact superpose eq119832 eq121709
    | exact resolve eq121709 eq119832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119832 eq121709
  have eq123921 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq121220 eq120238
    | exact resolve eq120238 eq121220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120238 eq121220
  have eq130885 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq123921 eq427
    | exact resolve eq427 eq123921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq123921
  have eq131005 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq130885
       have r₂ := eq28
       grind)
    | exact resolve eq130885 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130885
  have eq131031 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq119038 eq131005
    | exact resolve eq131005 eq119038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119038 eq131005
  have eq131051 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq131031
       have i₂ := eq121813
       grind)
    | exact superpose eq121813 eq131031
    | exact resolve eq131031 eq121813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121813 eq131031
  have eq131075 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq131051 eq15
    | exact resolve eq15 eq131051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131051
  have eq131444 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq131075
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq131075
    | exact resolve eq131075 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq131075
  have eq131581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120232 eq131444
    | exact resolve eq131444 eq120232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120232 eq131444
  have eq131667 : False := by grind
  exact eq131667

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_y_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq51 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51
    | (have j0 := eq51 x y
       grind)
    | exact resolve eq51 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq51 X0 X1
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq109
    | exact resolve eq109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq663 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq78 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq669 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq663 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq671 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq669 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq669 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq669 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq669 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq681 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq671 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq671
    | (have j0 := eq671 X0 X1
       grind)
    | exact resolve eq671 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq956 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 x X0 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq57
    | (have j0 := eq57 (σ x) X0 (σ y)
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq15227 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15227
    | exact resolve eq15227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15227
  have eq15245 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq15234
       have r₂ := eq28
       grind)
    | exact resolve eq15234 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15234
  have eq15247 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq15245
    | exact resolve eq15245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15245
  have eq15252 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq15259 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15247 eq55
    | exact resolve eq55 eq15247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15247
  have eq15293 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15259
    | exact resolve eq15259 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15259
  have eq15378 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15293
  have eq15656 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq666 x y
       have i₂ := eq15378
       grind)
    | exact superpose eq15378 eq666
    | (have j0 := eq666 x y
       grind)
    | exact resolve eq666 eq15378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15378
  have eq15659 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15656
  have eq15663 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15659
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15659
    | exact resolve eq15659 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15659
  have eq15676 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15663
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15663
    | exact resolve eq15663 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15663
  have eq15682 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15676
    | exact resolve eq15676 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15676
  have eq15683 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15682
  have eq15689 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15683
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15683
    | exact resolve eq15683 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15683
  have eq15695 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15689
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15689
    | exact resolve eq15689 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15689
  have eq15850 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15695 eq55
    | exact resolve eq55 eq15695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15695
  have eq15888 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15850
    | exact resolve eq15850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15850
  have eq15889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15888
  have eq16846 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15889 eq28
    | exact resolve eq28 eq15889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15889
  have eq17897 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq15252 eq117
    | exact resolve eq117 eq15252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq15252
  have eq17915 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17897
  have eq17944 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55 x x
       have i₂ := eq17915
       grind)
    | exact superpose eq17915 eq55
    | exact resolve eq55 eq17915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq17915
  have eq17985 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17944
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17944
    | exact resolve eq17944 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17944
  have eq17993 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17985 eq53
    | exact resolve eq53 eq17985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18411 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq17993 eq960
    | exact resolve eq960 eq17993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17993
  have eq18480 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53 eq18411
    | exact resolve eq18411 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18411
  have eq18487 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq18480
    | exact resolve eq18480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18480
  have eq18520 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18487 eq17985
    | exact resolve eq17985 eq18487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17985 eq18487
  have eq18521 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq18520
  have eq18644 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18521 eq30
    | exact resolve eq30 eq18521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18521
  have eq18796 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq18644
    | exact resolve eq18644 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18644
  have eq18824 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18796 eq29
    | exact resolve eq29 eq18796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq18796
  have eq18980 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq18824
    | exact resolve eq18824 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18824
  have eq18981 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18980
  have eq18982 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18981 eq21
    | exact resolve eq21 eq18981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18981
  have eq19109 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18982
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18982
    | exact resolve eq18982 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18982
  have eq19187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq19109 eq16846
    | (have r₁ := eq16846
       have r₂ := eq19109
       grind)
    | exact resolve eq16846 eq19109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16846
  have eq19205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19187
  have eq19206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19205
  have eq19398 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19206 eq53
    | exact resolve eq53 eq19206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19206
  have eq19677 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19398 eq960
    | exact resolve eq960 eq19398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960 eq19398
  have eq19747 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq53 eq19677
    | exact resolve eq19677 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq19677
  have eq19754 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq19747
    | exact resolve eq19747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19747
  have eq19763 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq19754 eq28
    | exact resolve eq28 eq19754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19754
  have eq19797 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq19763
       have r₂ := eq19109
       grind)
    | exact resolve eq19763 eq19109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19109 eq19763
  have eq19927 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq19797 eq52
    | exact resolve eq52 eq19797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20228 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq956 x
       have i₂ := eq19927
       grind)
    | exact superpose eq19927 eq956
    | exact resolve eq956 eq19927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq19927
  have eq20296 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq52 eq20228
    | exact resolve eq20228 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20228
  have eq20303 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq20296
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20296
    | exact resolve eq20296 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20296
  have eq20505 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq20303 eq19797
    | exact resolve eq19797 eq20303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19797 eq20303
  have eq20506 : x = y := by grind
  clear eq20505
  have eq20560 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20506
       grind)
    | exact superpose eq20506 eq19
    | exact resolve eq19 eq20506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20561 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20506
       grind)
    | exact superpose eq20506 eq25
    | exact resolve eq25 eq20506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20506
  have eq20677 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20561
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20561
    | exact resolve eq20561 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20561
  have eq20764 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20677 eq27
    | exact resolve eq27 eq20677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20677
  have eq20936 : x = (k (M.op x y) x) := by grind
  clear eq20560
  have eq21094 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20936 eq666
    | (have j0 := eq666 x (M.op x y)
       grind)
    | exact resolve eq666 eq20936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq21095 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20936 eq681
    | (have j0 := eq681 (M.op x y) x
       grind)
    | exact resolve eq681 eq20936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq20936
  have eq21097 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq21095
  have eq21098 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq21094
  have eq21102 : (σ x) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq21097
    | exact resolve eq21097 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21097
  have eq21103 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21 eq21098
    | exact resolve eq21098 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21098
  have eq21116 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21102
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21102
    | exact resolve eq21102 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21102
  have eq21117 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21103
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21103
    | exact resolve eq21103 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21103
  have eq21125 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21116
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21116
    | exact resolve eq21116 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21116
  have eq21126 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21117
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21117
    | exact resolve eq21117 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21117
  have eq21134 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20764 eq21125
    | exact resolve eq21125 eq20764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21125
  have eq21135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20764 eq21126
    | exact resolve eq21126 eq20764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21126
  have eq21141 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq21134
    | exact resolve eq21134 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21134
  have eq21142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq21135
    | exact resolve eq21135 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21135
  have eq21148 : (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq21141
       have r₂ := eq28
       grind)
    | exact resolve eq21141 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21141
  have eq21149 : (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq21142
       have r₂ := eq28
       grind)
    | exact resolve eq21142 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21142
  have eq21264 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21148 eq20764
    | exact resolve eq20764 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20764
  have eq21730 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21148 eq21149
    | exact resolve eq21149 eq21148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21148 eq21149
  have eq22033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21730 eq21264
    | exact resolve eq21264 eq21730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21264 eq21730
  have eq22034 : False := by grind
  exact eq22034

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 X1) X0
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq67
    | exact resolve eq67 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq107 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq109 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
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
  have eq679 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq696 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq705 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq679 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq679
    | (have j0 := eq679 X0
       grind)
    | exact resolve eq679 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq710 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq705 X0
       have j1 := eq696 X0
       grind)
    | (have r₁ := eq705 X0
       have r₂ := eq696 X0
       grind)
    | exact resolve eq705 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq705
  have eq712 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq710 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq710
    | exact resolve eq710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0) (σ X0)
       have i₂ := eq710 X0
       grind)
    | exact superpose eq710 eq67
    | exact resolve eq67 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq712 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq712
    | exact resolve eq712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq712
  have eq739 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq738 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq738
    | exact resolve eq738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq746 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107 x y
       grind)
    | exact superpose eq107 eq16
    | (have j1 := eq107 x y
       grind)
    | exact resolve eq16 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq780 : (σ y) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq746
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq746
    | exact resolve eq746 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq799 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq780
       have i₂ := eq739 x
       grind)
    | exact superpose eq739 eq780
    | exact resolve eq780 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq944 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq721 X0
       have i₂ := eq739 X0
       grind)
    | exact superpose eq739 eq721
    | exact resolve eq721 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq1036 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq944 X0
       grind)
    | exact superpose eq944 eq67
    | exact resolve eq67 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq944
  have eq13939 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq109
    | exact resolve eq109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq14196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13939 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13939
    | (have j0 := eq13939 X0 X1
       grind)
    | exact resolve eq13939 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13939
  have eq24442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq799
       have i₂ := eq14196 y x
       grind)
    | exact superpose eq14196 eq799
    | (have j1 := eq14196 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq799
       have r₂ := eq14196 y x
       grind)
    | (have r₁ := eq799
       have r₂ := eq14196 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq799
       have r₂ := eq14196 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq799 eq14196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq14196
  have eq24443 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq24442
  have eq24445 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24443
       grind)
    | exact superpose eq24443 eq16
    | exact resolve eq16 eq24443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24443
  have eq24446 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24445
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq24445
    | exact resolve eq24445 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24445
  have eq24447 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24446
       have i₂ := eq739 x
       grind)
    | exact superpose eq739 eq24446
    | exact resolve eq24446 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24446
  have eq24448 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq24447
  have eq24450 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24448
       grind)
    | exact superpose eq24448 eq10
    | exact resolve eq10 eq24448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24448
  have eq24579 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24450
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq24450
    | exact resolve eq24450 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24450
  have eq24605 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24579
       grind)
    | exact superpose eq24579 eq16
    | exact resolve eq16 eq24579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24579
  have eq24606 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24605
       have i₂ := eq710 x
       grind)
    | exact superpose eq710 eq24605
    | exact resolve eq24605 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq24605
  have eq24607 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24606
       have i₂ := eq739 x
       grind)
    | exact superpose eq739 eq24606
    | exact resolve eq24606 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq24606
  have eq24608 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq24607
  have eq24640 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq24608
       grind)
    | exact superpose eq24608 eq10
    | exact resolve eq10 eq24608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24608
  have eq24769 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24640
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq24640
    | exact resolve eq24640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24640
  have eq24770 : y = (M.op x x) := by grind
  clear eq24769
  have eq24800 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1036 x
       have i₂ := eq24770
       grind)
    | exact superpose eq24770 eq1036
    | exact resolve eq1036 eq24770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq24863 : y = (M.op x y) := by
    first
    | (have i₁ := eq69 x x
       have i₂ := eq24770
       grind)
    | exact superpose eq24770 eq69
    | exact resolve eq69 eq24770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq24770
  have eq25286 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24800
       grind)
    | exact superpose eq24800 eq16
    | exact resolve eq16 eq24800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24800
  have eq25369 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq25286
       have i₂ := eq24863
       grind)
    | exact superpose eq24863 eq25286
    | exact resolve eq25286 eq24863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24863 eq25286
  have eq25370 : False := by grind
  exact eq25370

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pxx_pxy_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq452 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq452 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq455 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq453 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq453 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq453 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq472 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq455 (σ X0)
       grind)
    | exact superpose eq455 eq15
    | exact resolve eq15 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq472 X0
       have i₂ := eq455 X0
       grind)
    | exact superpose eq455 eq472
    | exact resolve eq472 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq472
  have eq538 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0) (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq66
    | exact resolve eq66 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq547 X0 X1
       have j1 := eq548 X0 X1
       grind)
    | (have r₁ := eq547 X0 X1
       have r₂ := eq548 X0 X1
       grind)
    | exact resolve eq547 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq548
  have eq1055 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq549 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq549
    | exact resolve eq549 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq549 X1 (σ X0)
       grind)
    | exact superpose eq549 eq15
    | (have j1 := eq549 X1 (σ X0)
       grind)
    | exact resolve eq15 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq1085 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1066 X0 X1
       have i₂ := eq491 X0
       grind)
    | exact superpose eq491 eq1066
    | (have j0 := eq1066 X0 X1
       grind)
    | exact resolve eq1066 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491 eq1066
  have eq1103 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1055 (τ X1) X0
       grind)
    | exact superpose eq1055 eq19
    | (have j1 := eq1055 (τ X1) X0
       grind)
    | exact resolve eq19 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1055
  have eq1647 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1103
    | exact resolve eq1103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1759 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1647 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1647
    | (have j0 := eq1647 X0 X1
       grind)
    | exact resolve eq1647 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq2829 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1085 x y
       grind)
    | exact superpose eq1085 eq16
    | (have j1 := eq1085 x y
       grind)
    | exact resolve eq16 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq2979 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2829
       have i₂ := eq1759 y x
       grind)
    | exact superpose eq1759 eq2829
    | (have j1 := eq1759 y x
       grind)
    | (have r₁ := eq2829
       have r₂ := eq1759 y x
       grind)
    | exact resolve eq2829 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759 eq2829
  have eq2980 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2979
  have eq2991 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq538 x
       have i₂ := eq2980
       grind)
    | exact superpose eq2980 eq538
    | exact resolve eq538 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3021 : y = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq2980
       grind)
    | exact superpose eq2980 eq66
    | exact resolve eq66 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq3101 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2991
       grind)
    | exact superpose eq2991 eq16
    | exact resolve eq16 eq2991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991
  have eq3143 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3101
       have i₂ := eq3021
       grind)
    | exact superpose eq3021 eq3101
    | exact resolve eq3101 eq3021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021 eq3101
  have eq3144 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq3143
  have eq3145 : (σ y) = (σ (M.op x x)) := by grind
  clear eq3144
  have eq3150 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq538 x
       have i₂ := eq3145
       grind)
    | exact superpose eq3145 eq538
    | exact resolve eq538 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq3162 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq3145
       grind)
    | exact superpose eq3145 eq10
    | exact resolve eq10 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3218 : y = (M.op x x) := by
    first
    | (have i₁ := eq3162
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq3162
    | exact resolve eq3162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3256 : y = (M.op x y) := by
    first
    | (have i₁ := eq66 x x
       have i₂ := eq3218
       grind)
    | exact superpose eq3218 eq66
    | exact resolve eq66 eq3218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq3218
  have eq3339 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3150
       grind)
    | exact superpose eq3150 eq16
    | exact resolve eq16 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3367 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq3339
       have i₂ := eq3256
       grind)
    | exact superpose eq3256 eq3339
    | exact resolve eq3339 eq3256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256 eq3339
  have eq3368 : False := by grind
  exact eq3368

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyy_y_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq54 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq54
    | (have j0 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq54 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X0 X1) X0
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op (M.op (M.op X1 X2) X0) X1)) ∨ (M.op (M.op (M.op X1 X2) X0) X1) = (k X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq73 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq110 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq110
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq110 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq668 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq54
    | (have j1 := eq93 X0 X1
       grind)
    | exact resolve eq54 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq847 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X0) ≠ (M.op (M.op (M.op X0 X1) X2) X0) ∨ (M.op (M.op (M.op X0 X1) X2) X0) = (k X3 (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (M.op (M.op (M.op X0 X1) X2) X0) = (k X2 (M.op (M.op (M.op X0 X1) X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have i₂ := eq86 X0 X1 X2
       grind)
    | exact superpose eq86 eq13
    | (have j1 := eq86 X2 X0 X1
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X1)
       have r₂ := eq86 X0 X1 X2
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq848 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (k X3 (M.op (M.op (M.op X0 X1) X2) X0)) ∨ (M.op (M.op (M.op X0 X1) X2) X0) = (k X2 (M.op (M.op (M.op X0 X1) X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq847 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq882 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq60 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq60
    | (have j0 := eq60 x X0 y
       grind)
    | exact resolve eq60 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq60
    | (have j0 := eq60 (σ x) X0 (σ y)
       grind)
    | exact resolve eq60 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12283 : ∀ X0 : G, x = (k (M.op x y) x) ∨ x = (k X0 x) := by
    intro X0
    first
    | exact superpose eq62 eq848
    | exact resolve eq848 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq12286 : ∀ X0 : G, (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq64 eq848
    | exact resolve eq848 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq848
  have eq14549 : x ≠ x ∨ x = (k (M.op x y) x) := by
    first
    | (have j0 := eq12283 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12283
  have eq14550 : x = (k (M.op x y) x) := by grind
  clear eq14549
  have eq15041 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14550 eq668
    | (have j0 := eq668 x x
       grind)
    | exact resolve eq668 eq14550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq14550
  have eq15044 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq15041
  have eq15047 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15044
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15044
    | exact resolve eq15044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15044
  have eq15059 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq15047
    | exact resolve eq15047 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15047
  have eq15067 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15059
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15059
    | exact resolve eq15059 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15059
  have eq15881 : (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have j0 := eq12286 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12286
  have eq15882 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq15881
  have eq16117 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq15067 eq60
    | exact resolve eq60 eq15067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq15067
  have eq16168 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16117 x
       have i₂ := eq54 sF2 x
       grind)
    | exact superpose eq54 eq16117
    | exact resolve eq16117 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq16117
  have eq16631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have j0 := eq16168 (σ (M.op x y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168
  have eq16632 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq16631
  have eq21759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq21759
    | exact resolve eq21759 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21759
  have eq21778 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq21767
       have r₂ := eq27
       grind)
    | exact resolve eq21767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21767
  have eq21782 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq21778
    | exact resolve eq21778 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21778
  have eq21792 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq21782 eq886
    | exact resolve eq886 eq21782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq21782
  have eq21873 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56 eq21792
    | exact resolve eq21792 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq21792
  have eq21884 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq21873
    | exact resolve eq21873 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21873
  have eq21885 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21884
  have eq21895 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq882 x
       have i₂ := eq21885
       grind)
    | exact superpose eq21885 eq882
    | exact resolve eq882 eq21885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21885
  have eq21971 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55 eq21895
    | exact resolve eq21895 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21895
  have eq21979 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21971
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21971
    | exact resolve eq21971 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21971
  have eq21980 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21979
  have eq22012 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21980 eq15882
    | exact resolve eq15882 eq21980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15882 eq21980
  have eq22120 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq22012 eq123
    | exact resolve eq123 eq22012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq22012
  have eq22135 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq22120
  have eq23184 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq882 x
       have i₂ := eq22135
       grind)
    | exact superpose eq22135 eq882
    | exact resolve eq882 eq22135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22135
  have eq23260 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq55 eq23184
    | exact resolve eq23184 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23184
  have eq23268 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23260
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23260
    | exact resolve eq23260 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23260
  have eq23269 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq23268
  have eq23274 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23269 eq28
    | exact resolve eq28 eq23269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq23269
  have eq23447 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq23274
    | exact resolve eq23274 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq23274
  have eq23489 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23447 eq20
    | exact resolve eq20 eq23447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23447
  have eq23629 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq23489
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23489
    | exact resolve eq23489 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23489
  have eq23705 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23629 eq26
    | exact resolve eq26 eq23629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23629
  have eq23836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16632 eq23705
    | exact resolve eq23705 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23705
  have eq23873 : x = (M.op x y) := by
    first
    | (have r₁ := eq23836
       have r₂ := eq27
       grind)
    | exact resolve eq23836 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23836
  have eq23893 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23873 eq20
    | exact resolve eq20 eq23873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq23896 : x = (M.op x x) := by
    first
    | exact superpose eq23873 eq55
    | exact resolve eq55 eq23873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24051 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23893
    | exact resolve eq23893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23893
  have eq24357 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq882 x
       have i₂ := eq23896
       grind)
    | exact superpose eq23896 eq882
    | exact resolve eq882 eq23896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq23896
  have eq24433 : y = (M.op x y) := by
    first
    | exact superpose eq55 eq24357
    | exact resolve eq24357 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq24357
  have eq24441 : y = (M.op x y) := by
    first
    | (have i₁ := eq24433
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24433
    | exact resolve eq24433 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24433
  have eq24443 : x = y := by
    first
    | exact superpose eq23873 eq24441
    | exact resolve eq24441 eq23873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23873 eq24441
  have eq24449 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq24443
       grind)
    | exact superpose eq24443 eq24
    | exact resolve eq24 eq24443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24443
  have eq24580 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24449
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24449
    | exact resolve eq24449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24449
  have eq24634 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24051 eq24580
    | exact resolve eq24580 eq24051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24051 eq24580
  have eq24747 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq24634 eq26
    | exact resolve eq26 eq24634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24634
  have eq24889 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16632 eq24747
    | exact resolve eq24747 eq16632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16632 eq24747
  have eq24943 : False := by grind
  exact eq24943

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq35 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq22 (τ X0) (τ X0)
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq47 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46
    | (have j0 := eq46 X0
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq173 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (σ X2)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq74
    | (have j0 := eq74 X2 X2
       grind)
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq185 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq476 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq47 (σ X0)
       grind)
    | exact superpose eq47 eq36
    | (have j1 := eq47 (σ X0)
       grind)
    | exact resolve eq36 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq483 : ∀ X0 : G, (τ (σ X0)) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq476 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq476
    | (have j0 := eq476 X0
       grind)
    | exact resolve eq476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq499 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq483 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq483
    | (have j0 := eq483 X0
       grind)
    | exact resolve eq483 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq512 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq499 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq499
    | (have j0 := eq499 X0
       grind)
    | exact resolve eq499 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq761 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq76 (τ X0) X0
       grind)
    | exact superpose eq76 eq47
    | (have j0 := eq47 X0
       have j1 := eq76 (τ X0) X0
       grind)
    | exact resolve eq47 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq781 : ∀ X0 : G, (k (k X0 (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq787 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq781 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq781
    | (have j0 := eq781 X0
       grind)
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq862 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq787 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq787
    | (have j0 := eq787 (σ X0)
       grind)
    | exact resolve eq787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq896 : ∀ X0 : G, (σ X0) = (σ (k (k (τ (σ X0)) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq862 X0
       have i₂ := eq35 (σ X0) X0 X0
       grind)
    | exact superpose eq35 eq862
    | (have j0 := eq862 X0
       grind)
    | exact resolve eq862 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq862
  have eq897 : ∀ X0 : G, (σ X0) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq896 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq896
    | (have j0 := eq896 X0
       grind)
    | exact resolve eq896 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1387 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq897 X0
       have i₂ := eq14 (k X0 X0) X0
       grind)
    | exact superpose eq14 eq897
    | (have j0 := eq897 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq897 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq1410 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387
  have eq1431 : ∀ X0 : G, (σ X0) = (σ (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1410 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1410 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq1410 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq2041 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 X0)) ∨ (k (σ X1) X2) = (σ (k X0 X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X0 X1 X1
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq173
    | (have j0 := eq173 X1 X2 X0
       have j1 := eq74 X0 X0
       grind)
    | exact resolve eq173 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq173
  have eq2068 : ∀ X0 X1 X2 : G, (σ X0) = (σ (k X0 X0)) ∨ (k (σ X1) X2) = (σ (k X0 X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2041 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2079 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2068 X0 X1 X2
       have j1 := eq186 X0
       grind)
    | (have r₁ := eq2068 X0 X1 X2
       have r₂ := eq186 X0
       grind)
    | exact resolve eq2068 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq2068
  have eq3816 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 (k X0 X0))
       have i₂ := eq1431 X0
       grind)
    | exact superpose eq1431 eq10
    | (have j1 := eq1431 X0
       grind)
    | exact resolve eq10 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1431
  have eq3861 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3816 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3816
    | (have j0 := eq3816 X0
       grind)
    | exact resolve eq3816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816
  have eq4057 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq24 X0 (k X0 X0)
       have i₂ := eq3861 X0
       grind)
    | exact superpose eq3861 eq24
    | (have j1 := eq3861 X0
       grind)
    | exact resolve eq24 eq3861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3861
  have eq4143 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4057 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq4057 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq4057 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057
  have eq4198 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4143 (σ X0)
       grind)
    | exact superpose eq4143 eq15
    | exact resolve eq15 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4205 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0 X0
       have i₂ := eq4143 (τ X0)
       grind)
    | exact superpose eq4143 eq48
    | exact resolve eq48 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4214 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4205 X0
       have i₂ := eq4143 X0
       grind)
    | exact superpose eq4143 eq4205
    | exact resolve eq4205 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205
  have eq4221 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4198 X0
       have i₂ := eq4143 X0
       grind)
    | exact superpose eq4143 eq4198
    | exact resolve eq4198 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq4305 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = X0 ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq47
    | exact resolve eq47 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq4312 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 X0)) (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq512 (τ X0)
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq512
    | exact resolve eq512 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq4358 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq4312 X0
       have i₂ := eq48 X0 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq4312
    | (have j0 := eq4312 X0
       grind)
    | exact resolve eq4312 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4312
  have eq4364 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4305 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4305
    | (have j0 := eq4305 X0
       grind)
    | exact resolve eq4305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4305
  have eq4435 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq4221 X0
       grind)
    | exact superpose eq4221 eq24
    | exact resolve eq24 eq4221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221
  have eq11782 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k (M.op X0 X0) X1)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1 (M.op X0 X0)
       have i₂ := eq4364 X0
       grind)
    | exact superpose eq4364 eq48
    | (have j1 := eq4364 X0
       grind)
    | exact resolve eq48 eq4364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4364
  have eq11840 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (M.op X0 X0) X1)) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11782 X0 X1
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq11782
    | (have j0 := eq11782 X0 X1
       grind)
    | exact resolve eq11782 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11782
  have eq194458 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (k (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X1)
       have i₂ := eq11840 X0 X1
       grind)
    | exact superpose eq11840 eq11
    | (have j1 := eq11840 X0 X1
       grind)
    | exact resolve eq11 eq11840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11840
  have eq194642 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = X0 ∨ (k X0 X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq194458 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq194458
    | (have j0 := eq194458 X0 X1
       grind)
    | exact resolve eq194458 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194458
  have eq194805 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq194642 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194642
  have eq194811 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq194805 X0
       have i₂ := eq4143 X0
       grind)
    | exact superpose eq4143 eq194805
    | (have j0 := eq194805 X0
       grind)
    | exact resolve eq194805 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194805
  have eq194863 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq194811 X0
       have i₂ := eq4143 X0
       grind)
    | exact superpose eq4143 eq194811
    | (have j0 := eq194811 X0
       grind)
    | exact resolve eq194811 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194811
  have eq197244 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq194863 (τ X0)
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq194863
    | exact resolve eq194863 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194863
  have eq197308 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ (k (M.op X0 X0) X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq197244 X0
       have i₂ := eq48 X0 (M.op X0 X0)
       grind)
    | exact superpose eq48 eq197244
    | (have j0 := eq197244 X0
       grind)
    | exact resolve eq197244 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq197244
  have eq243762 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq197308 X0
       have i₂ := eq4358 X0
       grind)
    | exact superpose eq4358 eq197308
    | (have j1 := eq4358 X0
       grind)
    | (have r₁ := eq197308 X0
       have r₂ := eq4358 X0
       grind)
    | exact resolve eq197308 eq4358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4358 eq197308
  have eq243769 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq243762 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243762
  have eq243770 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq243769 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243769
  have eq244155 : ∀ X0 : G, (σ (τ X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X0)
       have i₂ := eq243770 X0
       grind)
    | exact superpose eq243770 eq11
    | exact resolve eq11 eq243770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243770
  have eq244352 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq244155 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq244155
    | exact resolve eq244155 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244155
  have eq247772 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k (σ (M.op (τ X0) (τ X0))) X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2079 X1 (M.op (τ X0) (τ X0)) X0
       have i₂ := eq244352 (τ X0)
       grind)
    | exact superpose eq244352 eq2079
    | (have j0 := eq2079 X1 (M.op (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq2079 eq244352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079
  have eq247836 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k (σ (τ (M.op X0 X0))) X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq247772 X0 X1
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq247772
    | (have j0 := eq247772 X0 X1
       grind)
    | exact resolve eq247772 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247772
  have eq247957 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) (k (M.op X0 X0) X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq247836 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq247836
    | (have j0 := eq247836 X0 X1
       grind)
    | exact resolve eq247836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247836
  have eq248046 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq247957 X0 X1
       have i₂ := eq244352 X0
       grind)
    | exact superpose eq244352 eq247957
    | (have j0 := eq247957 X0 X1
       grind)
    | exact resolve eq247957 eq244352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247957
  have eq248130 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq248046 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq248046
    | (have j0 := eq248046 X0 X1
       grind)
    | exact resolve eq248046 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248046
  have eq248153 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq248130 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq248130 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq248130 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248130
  have eq248163 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq248153 X0 X1
       have i₂ := eq4143 X1
       grind)
    | exact superpose eq4143 eq248153
    | (have j0 := eq248153 X0 X1
       grind)
    | exact resolve eq248153 eq4143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143 eq248153
  have eq248173 : ∀ X0 X1 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq248163 X0 X1
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq248163
    | (have j0 := eq248163 X0 X1
       grind)
    | exact resolve eq248163 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248163
  have eq248183 : ∀ X0 X1 : G, (k (M.op X0 X0) X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq248173 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq248173
    | (have j0 := eq248173 X0 X1
       grind)
    | exact resolve eq248173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248173
  have eq248193 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq248183 X0 X1
       have i₂ := eq244352 X0
       grind)
    | exact superpose eq244352 eq248183
    | (have j0 := eq248183 X0 X1
       grind)
    | exact resolve eq248183 eq244352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244352 eq248183
  have eq257366 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq248193 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq248193
    | (have j0 := eq248193 X1 (τ X0)
       grind)
    | exact resolve eq248193 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257875 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq248193 (σ X1) X0
       grind)
    | exact superpose eq248193 eq15
    | (have j1 := eq248193 (σ X1) X0
       grind)
    | exact resolve eq15 eq248193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248193
  have eq258358 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq257366 X0 X1
       have i₂ := eq4214 X0
       grind)
    | exact superpose eq4214 eq257366
    | (have j0 := eq257366 X0 X1
       grind)
    | exact resolve eq257366 eq4214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214 eq257366
  have eq258618 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq258358 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq258358
    | (have j0 := eq258358 X0 X1
       grind)
    | exact resolve eq258358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258358
  have eq261613 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq258618 X0 (τ X1)
       grind)
    | exact superpose eq258618 eq18
    | (have j1 := eq258618 X0 (τ X1)
       grind)
    | exact resolve eq18 eq258618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq258618
  have eq267507 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq261613 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq261613
    | exact resolve eq261613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261613
  have eq268127 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq267507 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq267507
    | (have j0 := eq267507 X0 X1
       grind)
    | exact resolve eq267507 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267507
  have eq278892 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq257875 x y
       grind)
    | exact superpose eq257875 eq16
    | (have j1 := eq257875 x y
       grind)
    | exact resolve eq16 eq257875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257875
  have eq280746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq278892
       have i₂ := eq268127 y x
       grind)
    | exact superpose eq268127 eq278892
    | (have j1 := eq268127 y x
       grind)
    | (have r₁ := eq278892
       have r₂ := eq268127 y x
       grind)
    | exact resolve eq278892 eq268127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268127 eq278892
  have eq280749 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq280746
  have eq282331 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq280749
       grind)
    | exact superpose eq280749 eq10
    | exact resolve eq10 eq280749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280749
  have eq282589 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq282331
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq282331
    | exact resolve eq282331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282331
  have eq282590 : y = (M.op x x) := by grind
  clear eq282589
  have eq282721 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4435 x
       have i₂ := eq282590
       grind)
    | exact superpose eq282590 eq4435
    | exact resolve eq4435 eq282590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq282906 : y = (M.op x y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq282590
       grind)
    | exact superpose eq282590 eq24
    | exact resolve eq24 eq282590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq282590
  have eq294294 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq282721
       grind)
    | exact superpose eq282721 eq16
    | exact resolve eq16 eq282721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282721
  have eq294449 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq294294
       have i₂ := eq282906
       grind)
    | exact superpose eq282906 eq294294
    | exact resolve eq294294 eq282906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282906 eq294294
  have eq294450 : False := by grind
  exact eq294450
