import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pyx_pyy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq82 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq72 y x
       grind)
    | exact superpose eq72 eq69
    | (have j1 := eq72 y x
       grind)
    | exact resolve eq69 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq122 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq72 sF1 (σ X0)
       grind)
    | exact superpose eq72 eq37
    | (have j1 := eq72 (σ (M.op x y)) x
       grind)
    | exact resolve eq37 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq375 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq377 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq375 X0 x x X3
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq679 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq104 eq72
    | (have j0 := eq72 (σ y) x
       grind)
    | exact resolve eq72 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq679
    | exact resolve eq679 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq683 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq680
       have r₂ := eq27
       grind)
    | exact resolve eq680 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq690 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq683 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq683
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq683
       grind)
    | exact resolve eq13 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq713 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq691 eq82
    | exact resolve eq82 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq691
  have eq826 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq683 eq713
    | exact resolve eq713 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq713
  have eq839 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by grind
  clear eq826
  have eq841 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq839
    | exact resolve eq839 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq839
  have eq846 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq72 y y
       have i₂ := eq841
       grind)
    | exact superpose eq841 eq72
    | (have j0 := eq72 y x
       grind)
    | exact resolve eq72 eq841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq841
  have eq847 : y = (M.op y y) := by grind
  clear eq846
  have eq856 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq847
       grind)
    | exact resolve eq13 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq14
    | exact resolve eq14 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq863 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq860 X0
       have i₂ := eq377 y X0
       grind)
    | (have i₁ := eq860 X0
       have i₂ := eq377 y (M.op y X0)
       grind)
    | exact superpose eq377 eq860
    | exact resolve eq860 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq893 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq861 y
       grind)
    | exact superpose eq861 eq70
    | exact resolve eq70 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq900 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq893
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq893
    | exact resolve eq893 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq901 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq900
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq900
    | exact resolve eq900 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq972 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq863 X0
       grind)
    | exact superpose eq863 eq14
    | exact resolve eq14 eq863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq972 X0
       have i₂ := eq847
       grind)
    | exact superpose eq847 eq972
    | exact resolve eq972 eq847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847 eq972
  have eq981 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq863 X0
       have i₂ := eq977 X0
       grind)
    | exact superpose eq977 eq863
    | exact resolve eq863 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq1007 : y = (M.op x y) := by
    first
    | (have i₁ := eq981 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq981
    | (have j0 := eq981 x
       grind)
    | exact resolve eq981 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq981
  have eq1049 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1007 eq20
    | exact resolve eq20 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1073 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1049
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1049
    | exact resolve eq1049 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1077 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1073 eq26
    | exact resolve eq26 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1120 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1007 eq122
    | exact resolve eq122 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1148 : (σ (k y y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1120 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1120
    | (have j0 := eq1120 y
       grind)
    | exact resolve eq1120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1120
  have eq1155 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1073 eq1148
    | exact resolve eq1148 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1170 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq1155
    | exact resolve eq1155 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1155
  have eq1182 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq901 eq1170
    | exact resolve eq1170 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq1170
  have eq1192 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1073 eq1182
    | exact resolve eq1182 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq1182
  have eq1193 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1192
  have eq1219 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1193 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq1193
       grind)
    | exact resolve eq13 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1193 eq14
    | exact resolve eq14 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1224 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq1219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1226 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1223 X0
       have i₂ := eq377 sF1 (M.op sF1 X0)
       grind)
    | (have i₁ := eq1223 x
       have i₂ := eq377 sF1 x
       grind)
    | exact superpose eq377 eq1223
    | exact resolve eq1223 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq1223
  have eq1341 : (k x (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq1224 eq61
    | exact resolve eq61 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1224
  have eq1348 : (k x y) = (τ (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq1007 eq1341
    | exact resolve eq1341 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq1341
  have eq1354 : (M.op y x) = (τ (M.op (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq1348
       have i₂ := eq861 x
       grind)
    | exact superpose eq861 eq1348
    | exact resolve eq1348 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq1348
  have eq1360 : x = (τ (M.op (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq1354
       have i₂ := eq977 x
       grind)
    | exact superpose eq977 eq1354
    | exact resolve eq1354 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977 eq1354
  have eq1492 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1360 eq15
    | exact resolve eq15 eq1360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1513 : (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1492
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1492
    | exact resolve eq1492 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1492
  have eq1531 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1513 eq1226
    | exact resolve eq1226 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226 eq1513
  have eq1546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1077 eq1531
    | exact resolve eq1531 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq1531
  have eq1548 : False := by grind
  exact eq1548

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op (M.op X1 X0) X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X3) = (M.op (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0 X4
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op X1 (M.op (M.op X1 X0) X2)) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq70 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq73 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op (M.op X0 (M.op (M.op X0 X3) X4)) (M.op X0 X3)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq67 X0 x x X3 X4
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3) X0
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq73
    | exact resolve eq73 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 X0 x X0
       have i₂ := eq73 X0 X0 x
       grind)
    | exact superpose eq73 eq52
    | exact resolve eq52 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X0) X2)) (M.op X0 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq187 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq187
    | exact resolve eq187 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq205 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0 X0 X0
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq73
    | exact resolve eq73 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq206 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X0 X0 X1
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq52
    | exact resolve eq52 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq194
  have eq213 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq217 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq213 (τ X0)
       grind)
    | exact superpose eq213 eq18
    | exact resolve eq18 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq213
  have eq228 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq9
    | exact resolve eq9 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq205 X0
       grind)
    | exact resolve eq12 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq228 X0 X1
       have i₂ := eq72 (M.op X0 X0) X1
       grind)
    | (have i₁ := eq228 X0 X1
       have i₂ := eq72 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq72 eq228
    | exact resolve eq228 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq228
  have eq317 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq82 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq82 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq343 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq324 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq343 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq509 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq233 X0 X1
       grind)
    | exact superpose eq233 eq9
    | exact resolve eq9 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 X1
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq509
    | exact resolve eq509 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq528 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X1 X0
       have i₂ := eq517 X1 X0
       grind)
    | exact superpose eq517 eq233
    | exact resolve eq233 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq531 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X0
       have i₂ := eq517 X1 X0
       grind)
    | exact superpose eq517 eq9
    | exact resolve eq9 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq346 (M.op X0 X0) X1
       have i₂ := eq232 X0 (M.op X0 X0)
       grind)
    | exact superpose eq232 eq346
    | (have j0 := eq346 (M.op X0 X0) X1
       grind)
    | exact resolve eq346 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq346
  have eq926 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 X1
       have i₂ := eq205 X0
       grind)
    | exact superpose eq205 eq904
    | (have j0 := eq904 X0 X1
       grind)
    | exact resolve eq904 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq927 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq926 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq958 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq927 (τ X0) X0
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq927
    | exact resolve eq927 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq927
  have eq1026 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq958 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq958
    | exact resolve eq958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1347 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq528 X0 (σ X0)
       have i₂ := eq1026 X0
       grind)
    | exact superpose eq1026 eq528
    | exact resolve eq528 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4385 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq317
       have i₂ := eq1026 x
       grind)
    | exact superpose eq1026 eq317
    | exact resolve eq317 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq4386 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4385
       have i₂ := eq1026 y
       grind)
    | exact superpose eq1026 eq4385
    | exact resolve eq4385 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq4385
  have eq4920 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4386
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq4386
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq4386 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4386
  have eq4921 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq4920
  have eq38225 : (M.op y y) = (τ (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4921
       grind)
    | exact superpose eq4921 eq10
    | exact resolve eq10 eq4921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4921
  have eq38322 : y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq38225
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq38225
    | exact resolve eq38225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38225
  have eq38323 : (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq38322
  have eq40685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 (M.op (M.op X0 X0) X1)) (M.op X0 X2)) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X0 (M.op X0 X2)
       have i₂ := eq204 X0 X0 X1 X2
       grind)
    | exact superpose eq204 eq9
    | exact resolve eq9 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq40749 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40685 X0 X1 X2
       have i₂ := eq517 X0 X1
       grind)
    | exact superpose eq517 eq40685
    | exact resolve eq40685 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40685
  have eq41082 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40749 (M.op (M.op X0 X0) (M.op X0 X1)) X2 X0
       have i₂ := eq206 X0 X1
       grind)
    | exact superpose eq206 eq40749
    | exact resolve eq40749 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq40749
  have eq41298 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41082 X0 X1 X2
       have i₂ := eq517 X0 (M.op X0 X1)
       grind)
    | exact superpose eq517 eq41082
    | exact resolve eq41082 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq41082
  have eq772406 : (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq38323
       grind)
    | exact superpose eq38323 eq10
    | exact resolve eq10 eq38323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38323
  have eq772919 : y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq772406
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq772406
    | exact resolve eq772406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772406
  have eq772920 : y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq772919
  have eq773613 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq41298 y y X0
       have i₂ := eq772920
       grind)
    | exact superpose eq772920 eq41298
    | exact resolve eq41298 eq772920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41298 eq772920
  have eq773628 : ∀ X0 : G, y = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq773613 X0
       have i₂ := eq531 X0 y
       grind)
    | exact superpose eq531 eq773613
    | exact resolve eq773613 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq773613
  have eq773938 : ∀ X0 : G, y = (M.op y y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq205 x
       have i₂ := eq773628 X0
       grind)
    | exact superpose eq773628 eq205
    | (have j1 := eq773628 y
       grind)
    | exact resolve eq205 eq773628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq773628
  have eq782350 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have j0 := eq773938 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773938
  have eq782351 : y = (M.op y y) := by grind
  clear eq782350
  have eq782697 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq528 X0 y
       have i₂ := eq782351
       grind)
    | exact superpose eq782351 eq528
    | exact resolve eq528 eq782351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq782736 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1347 y x
       have i₂ := eq782351
       grind)
    | exact superpose eq782351 eq1347
    | exact resolve eq1347 eq782351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347 eq782351
  have eq798733 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq782736 (σ x)
       grind)
    | exact superpose eq782736 eq16
    | exact resolve eq16 eq782736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782736
  have eq799111 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq798733
       have i₂ := eq782697 x
       grind)
    | exact superpose eq782697 eq798733
    | exact resolve eq798733 eq782697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782697 eq798733
  have eq799112 : False := by grind
  exact eq799112

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq58
  have eq81 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq87
    | (have j0 := eq87 X0 X1
       grind)
    | exact resolve eq87 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq87
  have eq306 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq93 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq13 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq323 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq306 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq330 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq323 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq323 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq323 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq340 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq330 X0 X1
       have j1 := eq81 X0 (σ X1)
       grind)
    | (have r₁ := eq330 X0 X1
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq330 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq330
  have eq348 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq340 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq340
    | (have j0 := eq340 X0 X1
       grind)
    | exact resolve eq340 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq349 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq353 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq349 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq349
    | exact resolve eq349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq349 x y
       grind)
    | exact superpose eq349 eq16
    | exact resolve eq16 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq429 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq353 X0 (τ X1)
       grind)
    | exact superpose eq353 eq17
    | exact resolve eq17 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq353
  have eq453 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq429 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq429
    | exact resolve eq429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq465 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq453
    | exact resolve eq453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq487 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq365
       have i₂ := eq465 x y
       grind)
    | exact superpose eq465 eq365
    | exact resolve eq365 eq465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq465
  have eq488 : False := by grind
  exact eq488

/-- `Equation2536`: `x = (y ◇ ((y ◇ x) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pyx_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2536.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X0) X2)) X0) = X0 := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, y = (M.op (M.op x (M.op (M.op x y) X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, y = (M.op (M.op (M.op x (M.op (M.op x y) X0)) (M.op y X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op (M.op x (M.op (M.op x y) X0)) y) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq544 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op y X1)) := by
    intro X1
    first
    | exact superpose eq174 eq542
    | exact resolve eq542 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq542
  have eq549 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) (σ y)) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq551 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ y) (M.op (σ y) X1)) := by
    intro X1
    first
    | exact superpose eq175 eq549
    | exact resolve eq549 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq549
  have eq882 : (M.op x y) = (k x y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq892 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq903 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq903 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq903 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq905 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (k X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq904 X0
       grind)
    | exact superpose eq904 eq16
    | exact resolve eq16 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq992 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq882
       grind)
    | exact superpose eq882 eq40
    | exact resolve eq40 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq993 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq992
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq992
    | exact resolve eq992 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq995 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq993
    | exact resolve eq993 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq997 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq995
       have i₂ := eq904 y
       grind)
    | exact superpose eq904 eq995
    | exact resolve eq995 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq997 eq892
    | exact resolve eq892 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq892 eq997
  have eq1045 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq1038
       have r₂ := eq27
       grind)
    | exact resolve eq1038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq1049 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1045
       have i₂ := eq904 sF3
       grind)
    | exact superpose eq904 eq1045
    | exact resolve eq1045 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1054 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq1049 eq152
    | exact resolve eq152 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1049
  have eq1059 : y = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq1054
    | exact resolve eq1054 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq1060 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1059
  have eq1068 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1060
       grind)
    | exact superpose eq1060 eq40
    | exact resolve eq40 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1070 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq905 y X0
       have i₂ := eq1060
       grind)
    | exact superpose eq1060 eq905
    | exact resolve eq905 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1070 X0
       have i₂ := eq544 X0
       grind)
    | (have i₁ := eq1070 X0
       have i₂ := eq544 (M.op y X0)
       grind)
    | exact superpose eq544 eq1070
    | exact resolve eq1070 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1070
  have eq1073 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1068
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1068
    | exact resolve eq1068 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1081 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1073 eq905
    | exact resolve eq905 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq1083 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq551 eq1081
    | exact resolve eq1081 eq551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551 eq1081
  have eq1157 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1072 X0
       grind)
    | exact superpose eq1072 eq16
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1163 : ∀ X0 : G, (M.op (k y y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1157 X0
       have i₂ := eq904 y
       grind)
    | exact superpose eq904 eq1157
    | exact resolve eq1157 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1169 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1060 eq1163
    | exact resolve eq1163 eq1060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060 eq1163
  have eq1175 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1072 X0
       have i₂ := eq1169 X0
       grind)
    | exact superpose eq1169 eq1072
    | exact resolve eq1072 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072 eq1169
  have eq1187 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1175 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1207 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq1187 x
       grind)
    | exact superpose eq1187 eq18
    | (have j1 := eq1187 x
       grind)
    | exact resolve eq18 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1228 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1207 eq31
    | exact resolve eq31 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1264 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1228
    | exact resolve eq1228 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1265 : y = (M.op x y) ∨ x = y := by grind
  clear eq1264
  have eq1268 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq1265
       grind)
    | exact superpose eq1265 eq24
    | exact resolve eq24 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1295 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq1268
    | exact resolve eq1268 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1785 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1083 eq16
    | exact resolve eq16 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1796 : ∀ X0 : G, (M.op (k (σ y) (σ y)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1785 X0
       have i₂ := eq904 sF3
       grind)
    | exact superpose eq904 eq1785
    | exact resolve eq1785 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1801 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1073 eq1796
    | exact resolve eq1796 eq1073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073 eq1796
  have eq1807 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1801 eq1083
    | exact resolve eq1083 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq1801
  have eq1823 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq1807 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1858 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1823 eq26
    | (have j1 := eq1823 (σ x)
       grind)
    | exact resolve eq26 eq1823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq1874 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1858 eq27
    | exact resolve eq27 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858
  have eq1880 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1874
       have r₂ := eq1295
       grind)
    | exact resolve eq1874 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295 eq1874
  have eq1882 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1880 eq31
    | exact resolve eq31 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1880
  have eq1919 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1882
    | exact resolve eq1882 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1882
  have eq1920 : x = y := by grind
  clear eq1919
  have eq1938 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1920
       grind)
    | exact superpose eq1920 eq18
    | exact resolve eq18 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1939 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1920
       grind)
    | exact superpose eq1920 eq24
    | exact resolve eq24 eq1920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1920
  have eq1949 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1939
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1939
    | exact resolve eq1939 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1939
  have eq1950 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1938
       have i₂ := eq904 x
       grind)
    | exact superpose eq904 eq1938
    | exact resolve eq1938 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq1951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1949 eq26
    | exact resolve eq26 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1949
  have eq1988 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1951
       have i₂ := eq904 sF2
       grind)
    | exact superpose eq904 eq1951
    | exact resolve eq1951 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq1951
  have eq1991 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1950
       grind)
    | exact superpose eq1950 eq39
    | exact resolve eq39 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1950
  have eq1995 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1991
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1991
    | exact resolve eq1991 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1991
  have eq1997 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1988 eq1995
    | exact resolve eq1995 eq1988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988 eq1995
  have eq1999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1997
    | exact resolve eq1997 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1997
  have eq2001 : False := by grind
  exact eq2001

/-- `Equation258`: `x = ((x ◇ x) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pyx_y_pyx_Equation258 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law258 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law258.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq16 X0 (M.op X0 X0)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq38 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq39 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq41 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq43 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq47 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq118 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq155 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X0) X1)) = X0 ∨ (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (M.op (M.op X0 X0) X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (M.op (k X0 (M.op X1 X1)) X0) = X1 ∨ (M.op (M.op X1 X1) X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq28 X0 (M.op X1 X1)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op X1 X1)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq28 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq164 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq164
    | (have j0 := eq164 X0 X1
       grind)
    | (have r₁ := eq164 X0 X0
       have r₂ := eq155 X0
       grind)
    | exact resolve eq164 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq169 : ∀ X0 X1 : G, (M.op (k X0 (k X1 X1)) X0) = X1 ∨ (M.op (M.op X1 X1) X0) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq155 X1
       grind)
    | exact superpose eq155 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq170 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq158
       have i₂ := eq155 sF2
       grind)
    | exact superpose eq155 eq158
    | exact resolve eq158 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq171 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq157
       have i₂ := eq155 x
       grind)
    | exact superpose eq155 eq157
    | exact resolve eq157 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq172 : ∀ X0 X1 : G, (k X1 (M.op (k X0 X0) X1)) = X0 ∨ (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq156 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq156
    | (have j0 := eq156 X0 X1
       grind)
    | exact resolve eq156 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq173 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X0) ∨ (M.op X0 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq165 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq165
    | (have j0 := eq165 X0 X1
       grind)
    | exact resolve eq165 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (k X0 (k X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq155 (M.op X1 X1)
       grind)
    | exact superpose eq155 eq169
    | (have j0 := eq169 X0 X1
       grind)
    | exact resolve eq169 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq178 : ∀ X0 X1 : G, (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = X0 ∨ (k X1 (M.op (k X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq172 X0 X1
       have i₂ := eq155 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq155 eq172
    | (have j0 := eq172 X0 X1
       grind)
    | exact resolve eq172 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq180 : ∀ X0 X1 : G, (M.op (k X1 X1) X0) = (k (k X1 X1) (k X1 X1)) ∨ (M.op (k X0 (k X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X0
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 X1 : G, (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) = X0 ∨ (k X1 (M.op (k X0 X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq178
    | (have j0 := eq178 X0 X1
       grind)
    | exact resolve eq178 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq183 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq35
    | exact resolve eq35 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq185 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq16
    | exact resolve eq16 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op X0 X0)
       have i₂ := eq155 (M.op X0 X0)
       grind)
    | exact superpose eq155 eq16
    | exact resolve eq16 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (k (k X0 X0) (k X0 X0)) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq186
    | exact resolve eq186 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq188 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq155 X1
       grind)
    | exact superpose eq155 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | (have r₁ := eq183 X0 X0
       have r₂ := eq155 X0
       grind)
    | exact resolve eq183 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq356 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq413 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq41 X1 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq171
       grind)
    | exact superpose eq171 eq42
    | exact resolve eq42 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq446
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq446
    | exact resolve eq446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq449 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq20 eq447
    | exact resolve eq447 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq451 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq356 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq356
    | exact resolve eq356 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq532 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq449 eq170
    | exact resolve eq170 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq532
       have r₂ := eq27
       grind)
    | exact resolve eq532 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq543 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq539 eq100
    | exact resolve eq100 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq539 eq185
    | exact resolve eq185 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 : G, x = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X0) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq185 x X0
       have i₂ := eq543
       grind)
    | exact superpose eq543 eq185
    | exact resolve eq185 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X1 X1) = (k X0 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
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
  have eq626 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq626
       have i₂ := eq155 sF2
       grind)
    | exact superpose eq155 eq626
    | exact resolve eq626 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq633 : (M.op x y) ≠ (k x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq624
       have i₂ := eq155 x
       grind)
    | exact superpose eq155 eq624
    | exact resolve eq624 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq637 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (k X0 X0) = (k X1 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq155 X1
       grind)
    | exact superpose eq155 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | (have r₁ := eq620 X0 X0
       have r₂ := eq155 X0
       grind)
    | exact resolve eq620 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq639 : (k (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq631
       have i₂ := eq155 sF3
       grind)
    | exact superpose eq155 eq631
    | exact resolve eq631 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq641 : (k y y) = (M.op x x) ∨ (M.op x y) ≠ (k x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq633
       have i₂ := eq155 y
       grind)
    | exact superpose eq155 eq633
    | exact resolve eq633 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq646 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq639
       have i₂ := eq155 sF2
       grind)
    | exact superpose eq155 eq639
    | exact resolve eq639 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq648 : (M.op x y) ≠ (k x x) ∨ (k x x) = (k y y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq641
       have i₂ := eq155 x
       grind)
    | exact superpose eq155 eq641
    | exact resolve eq641 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq1073 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq539 eq646
    | (have r₁ := eq646
       have r₂ := eq539
       grind)
    | exact resolve eq646 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1074 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by grind
  clear eq1073
  have eq1075 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq449 eq1074
    | exact resolve eq1074 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1077 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq1075 eq118
    | exact resolve eq118 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq1075 eq185
    | exact resolve eq185 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1086 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq546 eq1081
    | exact resolve eq1081 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq1081
  have eq1090 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq648
       have i₂ := eq1086
       grind)
    | exact superpose eq1086 eq648
    | (have r₁ := eq648
       have r₂ := eq1086
       grind)
    | exact resolve eq648 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq1092 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq1086
       grind)
    | exact superpose eq1086 eq42
    | exact resolve eq42 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq185 x X0
       have i₂ := eq1086
       grind)
    | exact superpose eq1086 eq185
    | exact resolve eq185 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : (M.op x y) = (k y y) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1090
  have eq1100 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1092
    | exact resolve eq1092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1102 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1100
    | exact resolve eq1100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1119 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1102 eq185
    | exact resolve eq185 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1168 : (σ x) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1119 sF1
       have i₂ := eq155 sF1
       grind)
    | exact superpose eq155 eq1119
    | exact resolve eq1119 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1197 : ∀ X0 : G, y = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq185 y X0
       have i₂ := eq1077
       grind)
    | exact superpose eq1077 eq185
    | exact resolve eq185 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077
  have eq1202 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq557 eq1197
    | exact resolve eq1197 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq1197
  have eq1210 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq42 x
       have i₂ := eq1202
       grind)
    | exact superpose eq1202 eq42
    | exact resolve eq42 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1218 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1210
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1210
    | exact resolve eq1210 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1220 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq1218
    | exact resolve eq1218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1237 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1220 eq185
    | exact resolve eq185 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1277 : (σ x) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1237 (k sF1 sF1)
       have i₂ := eq184 sF1
       grind)
    | exact superpose eq184 eq1237
    | exact resolve eq1237 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1283 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1277
       have i₂ := eq155 (k sF1 sF1)
       grind)
    | exact superpose eq155 eq1277
    | exact resolve eq1277 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277
  have eq1510 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) X0) X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1283 eq185
    | exact resolve eq185 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1524 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X1) = (k (M.op X0 X2) (M.op X0 X2)) ∨ (M.op (k X0 X0) X1) = (k X2 (M.op X0 X2)) ∨ (k X1 (M.op (k X0 X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 (M.op (k X0 X0) X1) X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq181
    | (have j0 := eq181 X0 X1
       have j1 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1561 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X1) = (M.op (k X2 X0) X2) ∨ (k X0 X0) = (M.op X0 X2) ∨ (k X1 (M.op (k X0 X0) X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X0 (M.op (k X0 X0) X1)
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq180
    | (have j1 := eq181 X0 X1
       grind)
    | exact resolve eq180 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq181
  have eq1688 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq26 eq1510
    | (have j0 := eq1510 (σ y)
       grind)
    | exact resolve eq1510 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1750 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq1098
       grind)
    | exact superpose eq1098 eq43
    | exact resolve eq43 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1755 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) X0) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq185 y X0
       have i₂ := eq1098
       grind)
    | exact superpose eq1098 eq185
    | exact resolve eq185 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1762 : x = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1094 eq1755
    | exact resolve eq1755 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1755
  have eq1764 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1750
    | exact resolve eq1750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1766 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq1764
    | exact resolve eq1764 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1770 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq39
    | exact resolve eq39 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq1778 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1770
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1770
    | exact resolve eq1770 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770
  have eq1783 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1778 eq170
    | exact resolve eq170 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1778 eq173
    | (have j0 := eq173 (σ x) (σ y)
       grind)
    | exact resolve eq173 eq1778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq1794 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq1790
    | exact resolve eq1790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1798 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1220 eq1783
    | exact resolve eq1783 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1220 eq1794
    | exact resolve eq1794 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq1794
  have eq1802 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1798
       have r₂ := eq27
       grind)
    | exact resolve eq1798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1804 : (σ x) ≠ (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1800
       have r₂ := eq27
       grind)
    | exact resolve eq1800 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1838 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1802 eq1688
    | exact resolve eq1688 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq1839 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1838
  have eq1845 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq1839
    | exact resolve eq1839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1847 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1802 eq1845
    | exact resolve eq1845 eq1802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802 eq1845
  have eq1859 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1847 eq1283
    | exact resolve eq1283 eq1847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283 eq1847
  have eq1874 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1859
  have eq1884 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq1874
       have r₂ := eq1804
       grind)
    | exact resolve eq1874 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq1874
  have eq1892 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1884 eq32
    | exact resolve eq32 eq1884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1884
  have eq1924 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq30 eq1892
    | exact resolve eq1892 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq1925 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq1924
  have eq3511 : (σ y) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (k y x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1766 eq187
    | exact resolve eq187 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766
  have eq3519 : (σ y) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1925 eq3511
    | exact resolve eq3511 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq3511
  have eq3531 : (σ y) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1086 eq3519
    | exact resolve eq3519 eq1086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086 eq3519
  have eq3540 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1168 eq3531
    | exact resolve eq3531 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq3531
  have eq3541 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3540
  have eq3557 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3541 eq170
    | exact resolve eq170 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3559 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3541 eq449
    | exact resolve eq449 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449 eq3541
  have eq3571 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3557
  have eq3589 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3571 eq100
    | exact resolve eq100 eq3571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq4118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3559 eq3571
    | exact resolve eq3571 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559 eq3571
  have eq4143 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) := by grind
  clear eq4118
  have eq4161 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4143
       have r₂ := eq27
       grind)
    | exact resolve eq4143 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq4179 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3589
       have i₂ := eq4161
       grind)
    | exact superpose eq4161 eq3589
    | exact resolve eq3589 eq4161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589 eq4161
  have eq4200 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4179
  have eq4223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4200 eq14
    | exact resolve eq14 eq4200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4200
  have eq4241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq4223
    | exact resolve eq4223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq4242 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4241
       have r₂ := eq27
       grind)
    | exact resolve eq4241 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4241
  have eq4243 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4242 eq29
    | exact resolve eq29 eq4242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4242
  have eq4266 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4243
    | exact resolve eq4243 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq4267 : x = (M.op x y) := by grind
  clear eq4266
  have eq4272 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq18
    | exact resolve eq18 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4273 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq22
    | exact resolve eq22 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4274 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq38
    | exact resolve eq38 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq4275 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq42
    | exact resolve eq42 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq4276 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq171
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq171
    | exact resolve eq171 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4277 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq543
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq543
    | exact resolve eq543 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq4312 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4273 eq20
    | exact resolve eq20 eq4273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4333 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq4273 eq413
    | exact resolve eq413 eq4273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq4402 : (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq4272 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | exact resolve eq12 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4405 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4402
       have i₂ := eq155 sF0
       grind)
    | exact superpose eq155 eq4402
    | exact resolve eq4402 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4402
  have eq4407 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have r₁ := eq4405
       have r₂ := eq4276
       grind)
    | exact resolve eq4405 eq4276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405
  have eq4409 : (k (M.op x y) (M.op x y)) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4407
       have i₂ := eq155 sF0
       grind)
    | exact superpose eq155 eq4407
    | exact resolve eq4407 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407
  have eq4410 : (k y y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq4409
       have i₂ := eq155 y
       grind)
    | exact superpose eq155 eq4409
    | exact resolve eq4409 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4409
  have eq4411 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq4276 eq4410
    | exact resolve eq4410 eq4276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4276 eq4410
  have eq5012 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq4411 eq39
    | exact resolve eq39 eq4411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4411
  have eq5019 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq20 eq5012
    | exact resolve eq5012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5012
  have eq5022 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq4312 eq5019
    | exact resolve eq5019 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5019
  have eq5107 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq5022 eq173
    | (have j0 := eq173 (σ x) (σ y)
       grind)
    | exact resolve eq173 eq5022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq5109 : (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq26 eq5107
    | exact resolve eq5107 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5107
  have eq5186 : (k (σ (M.op x y)) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4277 eq4275
    | exact resolve eq4275 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5193 : ∀ X0 : G, (M.op x y) = (M.op (M.op (τ (M.op (σ x) (σ y))) X0) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4277 eq185
    | exact resolve eq185 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5194 : (M.op x y) = (M.op (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4277 eq187
    | exact resolve eq187 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5197 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  have eq5200 : (M.op x y) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5194
       have i₂ := eq451 sF4 sF4
       grind)
    | exact superpose eq451 eq5194
    | exact resolve eq5194 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5204 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5186
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq5186
    | exact resolve eq5186 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5186
  have eq5208 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq5204
    | exact resolve eq5204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5204
  have eq5212 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4312 eq5208
    | exact resolve eq5208 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5208
  have eq5226 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5212 eq646
    | (have r₁ := eq646
       have r₂ := eq5212
       grind)
    | exact resolve eq646 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq5248 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5212 eq185
    | exact resolve eq185 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5254 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq5226
  have eq5723 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5248 (k sF4 sF4)
       have i₂ := eq184 sF4
       grind)
    | exact superpose eq184 eq5248
    | exact resolve eq5248 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5248
  have eq5729 : (σ x) = (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5723
       have i₂ := eq155 (k sF4 sF4)
       grind)
    | exact superpose eq155 eq5723
    | exact resolve eq5723 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723
  have eq7663 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5729 eq184
    | exact resolve eq184 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq7665 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ x)) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5729 eq187
    | exact resolve eq187 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq7671 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5212 eq7665
    | exact resolve eq7665 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7665
  have eq8070 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5254 eq118
    | exact resolve eq118 eq5254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq5254
  have eq8090 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5022 eq8070
    | exact resolve eq8070 eq5022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5022 eq8070
  have eq8094 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq8090
       have r₂ := eq5197
       grind)
    | exact resolve eq8090 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8090
  have eq9617 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (k X0 X0) ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5212 eq188
    | (have j0 := eq188 (σ x) X0
       grind)
    | exact resolve eq188 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq10090 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5729 eq9617
    | (have j0 := eq9617 (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq9617 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9617
  have eq10144 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq10090
  have eq10158 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7663 eq10144
    | exact resolve eq10144 eq7663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7663 eq10144
  have eq31565 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ≠ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7671 eq637
    | (have j0 := eq637 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq637 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq7671
       grind)
    | exact resolve eq637 eq7671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq7671
  have eq31587 : (k (σ x) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq31565
  have eq31604 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5212 eq31587
    | exact resolve eq31587 eq5212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5212 eq31587
  have eq33328 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31604 eq5200
    | exact resolve eq5200 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33384 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq33328
  have eq33406 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33384
       have i₂ := eq155 (τ sF4)
       grind)
    | exact superpose eq155 eq33384
    | exact resolve eq33384 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33384
  have eq33417 : (M.op x y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq33406
       have i₂ := eq451 sF4 sF4
       grind)
    | exact superpose eq451 eq33406
    | exact resolve eq33406 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33406
  have eq33422 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq31604 eq33417
    | exact resolve eq33417 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31604 eq33417
  have eq33426 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq33422
       have r₂ := eq5197
       grind)
    | exact resolve eq33422 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33422
  have eq33431 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq33426 eq4333
    | exact resolve eq4333 eq33426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53595 : ∀ X0 : G, (M.op (k x x) X0) = (M.op (M.op x y) y) ∨ (M.op x y) = (k x x) ∨ x = (k X0 (M.op (k x x) X0)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1561 x X0 y
       have i₂ := eq171
       grind)
    | exact superpose eq171 eq1561
    | (have j0 := eq1561 x X0 y
       grind)
    | exact resolve eq1561 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171 eq1561
  have eq53880 : ∀ X0 : G, (M.op x y) = (M.op (k x x) X0) ∨ (M.op x y) = (k x x) ∨ x = (k X0 (M.op (k x x) X0)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq4272 eq53595
    | (have j0 := eq53595 X0
       grind)
    | exact resolve eq53595 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53595
  have eq54045 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (k x x) ∨ x = (k X0 (M.op (k x x) X0)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq53880 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq53880
    | (have j0 := eq53880 X0
       grind)
    | exact resolve eq53880 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53880
  have eq54163 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ x = (k X0 (M.op (k x x) X0)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq54045 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq54045
    | (have j0 := eq54045 X0
       grind)
    | exact resolve eq54045 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54045
  have eq54242 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ x = (k X0 (M.op (k x x) X0)) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq4272 eq54163
    | (have j0 := eq54163 X0
       grind)
    | exact resolve eq54163 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54163
  have eq54266 : ∀ X0 : G, (M.op x y) = (k X0 (M.op (k (M.op x y) (M.op x y)) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq54242 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq54242
    | (have j0 := eq54242 X0
       grind)
    | exact resolve eq54242 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54242
  have eq54282 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k X0 (M.op (k (M.op x y) (M.op x y)) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq54266 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq54266
    | (have j0 := eq54266 X0
       grind)
    | exact resolve eq54266 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54266
  have eq54283 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k X0 (M.op (k (M.op x y) (M.op x y)) X0)) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq54282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54282
  have eq54296 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k X0 (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ (M.op x y) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq4277 eq54283
    | (have j0 := eq54283 X0
       grind)
    | exact resolve eq54283 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54283
  have eq54301 : ∀ X0 : G, (M.op x y) = (k X0 (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq4277 eq54296
    | (have j0 := eq54296 X0
       grind)
    | exact resolve eq54296 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54296
  have eq54550 : (σ (M.op x y)) = (k (σ x) (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq54301 eq4274
    | (have j1 := eq54301 (M.op x y)
       grind)
    | exact resolve eq4274 eq54301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq54559 : (σ (M.op x y)) = (k (σ x) (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq20 eq54550
    | exact resolve eq54550 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54550
  have eq54609 : (σ x) = (k (σ x) (σ (M.op (τ (M.op (σ x) (σ y))) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq4312 eq54559
    | exact resolve eq54559 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54559
  have eq55040 : (σ x) = (k (σ x) (σ (k (M.op x y) (τ (M.op (σ x) (σ y)))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq54609
       have i₂ := eq28 sF0 (τ sF4)
       grind)
    | exact superpose eq28 eq54609
    | (have j1 := eq28 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq54609 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54609
  have eq55089 : (σ x) = (k (σ x) (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq55040
       have i₂ := eq41 sF4 sF0
       grind)
    | exact superpose eq41 eq55040
    | exact resolve eq55040 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55040
  have eq55110 : (σ x) = (k (σ x) (k (σ (M.op x y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq20 eq55089
    | exact resolve eq55089 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55089
  have eq55128 : (σ x) = (k (σ x) (k (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq4312 eq55110
    | exact resolve eq55110 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55110
  have eq55138 : (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (k (σ x) (k (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq55128
       have i₂ := eq155 (τ sF4)
       grind)
    | exact superpose eq155 eq55128
    | exact resolve eq55128 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55128
  have eq55139 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (k (σ x) (k (σ x) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq55138
       have i₂ := eq451 sF4 sF4
       grind)
    | exact superpose eq451 eq55138
    | exact resolve eq55138 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55138
  have eq55140 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq33426 eq55139
    | exact resolve eq55139 eq33426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55139
  have eq55141 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq33426 eq55140
    | exact resolve eq55140 eq33426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33426 eq55140
  have eq55142 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33431 eq55141
    | exact resolve eq55141 eq33431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33431 eq55141
  have eq55143 : (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq55142
       have r₂ := eq5197
       grind)
    | exact resolve eq55142 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55142
  have eq55147 : (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq55143 eq54301
    | exact resolve eq54301 eq55143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54301
  have eq55150 : (M.op x y) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq55143 eq5193
    | exact resolve eq5193 eq55143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5193 eq55143
  have eq55154 : (M.op x y) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55150
  have eq55157 : (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq55147
  have eq55180 : (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | (have i₁ := eq55154
       have i₂ := eq28 sF0 (τ (k sF4 sF4))
       grind)
    | exact superpose eq28 eq55154
    | (have j1 := eq28 (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))
       grind)
    | exact resolve eq55154 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq55191 : (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55180
       have i₂ := eq155 (τ (k sF4 sF4))
       grind)
    | exact superpose eq155 eq55180
    | exact resolve eq55180 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55180
  have eq55193 : (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55191
       have i₂ := eq451 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq451 eq55191
    | exact resolve eq55191 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55191
  have eq55195 : (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55157 eq55193
    | exact resolve eq55193 eq55157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55157 eq55193
  have eq55196 : (k (M.op x y) (M.op x y)) = (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55195
       have i₂ := eq155 sF0
       grind)
    | exact superpose eq155 eq55195
    | exact resolve eq55195 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq55195
  have eq55197 : (τ (M.op (σ x) (σ y))) = (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4277 eq55196
    | exact resolve eq55196 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55196
  have eq55198 : (τ (σ x)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5729 eq55197
    | exact resolve eq55197 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55197
  have eq55199 : x = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq55198
    | exact resolve eq55198 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55198
  have eq55200 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq55199
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq55199
    | exact resolve eq55199 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55199
  have eq55201 : (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq55200
       have r₂ := eq5197
       grind)
    | exact resolve eq55200 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55200
  have eq55222 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq55201 eq41
    | exact resolve eq41 eq55201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq55201
  have eq55240 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq55222
    | exact resolve eq55222 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55222
  have eq55249 : (σ x) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4312 eq55240
    | exact resolve eq55240 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55240
  have eq55258 : (σ x) = (k (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq55249
       have r₂ := eq10158
       grind)
    | exact resolve eq55249 eq10158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10158 eq55249
  have eq55289 : (τ (σ x)) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq55258 eq4333
    | exact resolve eq4333 eq55258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4333 eq55258
  have eq55302 : x = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq55289
    | exact resolve eq55289 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55289
  have eq55304 : (M.op x y) = (k (M.op x y) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq55302
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq55302
    | exact resolve eq55302 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55302
  have eq62093 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5200 eq1524
    | (have j0 := eq1524 (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0 x
       grind)
    | exact resolve eq1524 eq5200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5200
  have eq62096 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (k (M.op x y) (M.op x y)) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq55154 eq1524
    | (have j0 := eq1524 (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) X0 x
       grind)
    | exact resolve eq1524 eq55154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524 eq55154
  have eq62324 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq62096 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62096
  have eq62403 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62324 X0
       have i₂ := eq451 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq451 eq62324
    | (have j0 := eq62324 X0
       grind)
    | exact resolve eq62324 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62324
  have eq62405 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62093 X0
       have i₂ := eq451 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq451 eq62093
    | (have j0 := eq62093 X0
       grind)
    | exact resolve eq62093 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62093
  have eq62504 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (k (M.op x y) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62403 X0
       have i₂ := eq451 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq451 eq62403
    | (have j0 := eq62403 X0
       grind)
    | exact resolve eq62403 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62403
  have eq62506 : ∀ X0 : G, (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (k (M.op x y) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (k (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62405 X0
       have i₂ := eq451 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq451 eq62405
    | (have j0 := eq62405 X0
       grind)
    | exact resolve eq62405 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62405
  have eq62569 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4277 eq62504
    | (have j0 := eq62504 X0
       grind)
    | exact resolve eq62504 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62504
  have eq62571 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (k (M.op x y) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62506 X0
       have i₂ := eq451 (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq451 eq62506
    | (have j0 := eq62506 X0
       grind)
    | exact resolve eq62506 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451 eq62506
  have eq62606 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (τ (σ x)) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5729 eq62569
    | (have j0 := eq62569 X0
       grind)
    | exact resolve eq62569 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62569
  have eq62608 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0)) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4277 eq62571
    | (have j0 := eq62571 X0
       grind)
    | exact resolve eq62571 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62571
  have eq62627 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op x X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq62606
    | (have j0 := eq62606 X0
       grind)
    | exact resolve eq62606 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62606
  have eq62629 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (τ (σ x)) X0)) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5729 eq62608
    | (have j0 := eq62608 X0
       grind)
    | exact resolve eq62608 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62608
  have eq62639 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62627 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq62627
    | (have j0 := eq62627 X0
       grind)
    | exact resolve eq62627 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62627
  have eq62641 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op x X0)) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq62629
    | (have j0 := eq62629 X0
       grind)
    | exact resolve eq62629 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62629
  have eq62650 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5729 eq62639
    | (have j0 := eq62639 X0
       grind)
    | exact resolve eq62639 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62639
  have eq62652 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (k (τ (M.op (σ x) (σ y))) (M.op x y)) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62641 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq62641
    | (have j0 := eq62641 X0
       grind)
    | exact resolve eq62641 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62641
  have eq62659 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq30 eq62650
    | (have j0 := eq62650 X0
       grind)
    | exact resolve eq62650 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62650
  have eq62661 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op (τ (σ x)) X0) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5729 eq62652
    | (have j0 := eq62652 X0
       grind)
    | exact resolve eq62652 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62652
  have eq62666 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq62659 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq62659
    | (have j0 := eq62659 X0
       grind)
    | exact resolve eq62659 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62659
  have eq62668 : ∀ X0 : G, (M.op x X0) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq62661
    | (have j0 := eq62661 X0
       grind)
    | exact resolve eq62661 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62661
  have eq62674 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62668 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq62668
    | (have j0 := eq62668 X0
       grind)
    | exact resolve eq62668 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62668
  have eq62679 : ∀ X0 : G, (M.op (M.op x y) X0) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5729 eq62674
    | (have j0 := eq62674 X0
       grind)
    | exact resolve eq62674 eq5729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5729 eq62674
  have eq62684 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x X0) ∨ (M.op (M.op x y) X0) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq62679
    | (have j0 := eq62679 X0
       grind)
    | exact resolve eq62679 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62679
  have eq62689 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (k (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62684 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq62684
    | (have j0 := eq62684 X0
       grind)
    | exact resolve eq62684 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62684
  have eq62694 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (k (τ (σ x)) (M.op x y)) = (M.op (M.op x y) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq62666 eq62689
    | (have j0 := eq62689 X0
       have j1 := eq62666 X0
       grind)
    | exact resolve eq62689 eq62666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62666 eq62689
  have eq62699 : ∀ X0 : G, (k x (M.op x y)) = (M.op (M.op x y) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq62694
    | (have j0 := eq62694 X0
       grind)
    | exact resolve eq62694 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62694
  have eq62703 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq62699 X0
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq62699
    | (have j0 := eq62699 X0
       grind)
    | exact resolve eq62699 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62699
  have eq62706 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4277 eq62703
    | (have j0 := eq62703 X0
       grind)
    | exact resolve eq62703 eq4277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277 eq62703
  have eq62707 : ∀ X0 : G, (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k X0 (M.op (M.op x y) X0)) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) X0) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq62706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62706
  have eq76723 : (σ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (k (σ y) (σ (M.op (M.op x y) y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq62707 eq39
    | (have j1 := eq62707 y
       grind)
    | exact resolve eq39 eq62707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq62707
  have eq76734 : (k (σ y) (σ (M.op x y))) = (σ (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4272 eq76723
    | exact resolve eq76723 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76723
  have eq76783 : (k (σ y) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq76734
       have i₂ := eq14 (k sF4 sF4)
       grind)
    | exact superpose eq14 eq76734
    | exact resolve eq76734 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76734
  have eq76807 : (k (σ y) (σ (M.op x y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq76783
    | exact resolve eq76783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76783
  have eq76828 : (k (σ y) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4312 eq76807
    | exact resolve eq76807 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76807
  have eq76845 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (k (σ y) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4272 eq76828
    | exact resolve eq76828 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4272 eq76828
  have eq76858 : (k (σ y) (σ x)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq76845
       have r₂ := eq5197
       grind)
    | exact resolve eq76845 eq5197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5197 eq76845
  have eq76870 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8094 eq76858
    | exact resolve eq76858 eq8094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8094 eq76858
  have eq76969 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq76870 eq55304
    | exact resolve eq55304 eq76870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55304 eq76870
  have eq77043 : (M.op x y) = (k (M.op x y) (τ (σ x))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq76969
  have eq77090 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq77043
    | exact resolve eq77043 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq77043
  have eq77121 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq77090
       have i₂ := eq4267
       grind)
    | exact superpose eq4267 eq77090
    | exact resolve eq77090 eq4267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4267 eq77090
  have eq77122 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq77121
  have eq77175 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq77122 eq4275
    | exact resolve eq4275 eq77122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4275
  have eq77188 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) X0) X0) := by
    intro X0
    first
    | exact superpose eq77122 eq185
    | exact resolve eq185 eq77122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77122
  have eq77259 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq77175
    | exact resolve eq77175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq77175
  have eq77288 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4312 eq77259
    | exact resolve eq77259 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77259
  have eq77363 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y y) := by
    first
    | exact superpose eq77288 eq5109
    | (have r₁ := eq5109
       have r₂ := eq77288
       grind)
    | exact resolve eq5109 eq77288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5109
  have eq77460 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq77363
  have eq77901 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq185 y X0
       have i₂ := eq77460
       grind)
    | exact superpose eq77460 eq185
    | exact resolve eq185 eq77460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq77460
  have eq77970 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77188 eq77901
    | exact resolve eq77901 eq77188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77188 eq77901
  have eq78046 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq77970 eq27
    | exact resolve eq27 eq77970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77970
  have eq78256 : y = (M.op x y) := by
    first
    | (have r₁ := eq78046
       have r₂ := eq4312
       grind)
    | exact resolve eq78046 eq4312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78046
  have eq78284 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq78256
       grind)
    | exact superpose eq78256 eq24
    | exact resolve eq24 eq78256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq78256
  have eq78405 : (σ x) = (σ y) := by
    first
    | exact superpose eq4273 eq78284
    | exact resolve eq78284 eq4273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273 eq78284
  have eq78497 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq78405 eq170
    | exact resolve eq170 eq78405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq78405
  have eq78596 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq78497
  have eq78638 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq77288 eq78596
    | exact resolve eq78596 eq77288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77288 eq78596
  have eq78689 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq78638 eq27
    | exact resolve eq27 eq78638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq78638
  have eq78898 : False := by grind
  exact eq78898

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxx_pyy_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
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
  have eq52 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq106 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq10
    | exact resolve eq10 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq43
    | exact resolve eq43 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq114 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq49
    | exact resolve eq49 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq115 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq114
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq114
    | exact resolve eq114 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq112
    | exact resolve eq112 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq111
    | exact resolve eq111 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq111
  have eq270 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq52 X0 (M.op X0 X0)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq870 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq118 X1
       grind)
    | exact superpose eq118 eq75
    | (have j0 := eq75 X0 X1
       grind)
    | exact resolve eq75 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq871 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1
       have i₂ := eq118 X1
       grind)
    | exact superpose eq118 eq870
    | (have j0 := eq870 X0 X1
       grind)
    | exact resolve eq870 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq870
  have eq1003 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq871 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq76209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76210 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq76209
    | exact resolve eq76209 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76209
  have eq76222 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq76210
       have r₂ := eq27
       grind)
    | exact resolve eq76210 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76210
  have eq76226 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq76222
    | exact resolve eq76222 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76222
  have eq76228 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq76226 eq106
    | (have r₁ := eq106
       have r₂ := eq76226
       grind)
    | exact resolve eq106 eq76226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq76324 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq76226
  have eq76326 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq76228
  have eq79876 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq76326
       have r₂ := eq76324
       grind)
    | exact resolve eq76326 eq76324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76324 eq76326
  have eq79882 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq79876 eq93
    | exact resolve eq93 eq79876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq79876
  have eq79896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq79882
  have eq79900 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq79896
       have r₂ := eq27
       grind)
    | exact resolve eq79896 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79896
  have eq79903 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq79900 eq115
    | exact resolve eq115 eq79900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79900
  have eq80036 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq79903
    | exact resolve eq79903 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79903
  have eq80037 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq80036
  have eq80049 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq80037
       grind)
    | exact superpose eq80037 eq105
    | (have r₁ := eq105
       have r₂ := eq80037
       grind)
    | exact resolve eq105 eq80037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq80050 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq80037
       grind)
    | exact superpose eq80037 eq117
    | exact resolve eq117 eq80037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80147 : x ≠ (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq80037
  have eq80149 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq80049
  have eq80178 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq80050
    | exact resolve eq80050 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80050
  have eq84387 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq80149
       have r₂ := eq80147
       grind)
    | exact resolve eq80149 eq80147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80147 eq80149
  have eq84402 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1003 x y
       have i₂ := eq84387
       grind)
    | exact superpose eq84387 eq1003
    | (have j0 := eq1003 x y
       grind)
    | exact resolve eq1003 eq84387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq84387
  have eq84406 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84402
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq84402
    | exact resolve eq84402 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84402
  have eq84420 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq84406
    | exact resolve eq84406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84406
  have eq84427 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq84420
       have r₂ := eq80178
       grind)
    | exact resolve eq84420 eq80178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84420
  have eq84432 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84427
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq84427
    | exact resolve eq84427 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84427
  have eq84437 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84432
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq84432
    | exact resolve eq84432 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84432
  have eq84442 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84437
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84437
    | exact resolve eq84437 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84437
  have eq84447 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq84442
    | exact resolve eq84442 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84442
  have eq84452 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84447
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq84447
    | exact resolve eq84447 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84447
  have eq84457 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq84452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq84452
    | exact resolve eq84452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84452
  have eq123383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq84457 eq80178
    | exact resolve eq80178 eq84457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80178 eq84457
  have eq123500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq123383
  have eq123531 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq123500
       have r₂ := eq27
       grind)
    | exact resolve eq123500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123500
  have eq123906 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq123531 eq115
    | exact resolve eq115 eq123531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq123531
  have eq124096 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq123906
    | exact resolve eq123906 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq123906
  have eq124097 : x = (M.op x x) := by grind
  clear eq124096
  have eq124111 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq124097
       grind)
    | exact superpose eq124097 eq117
    | exact resolve eq117 eq124097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq124122 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq270 x x
       have i₂ := eq124097
       grind)
    | exact superpose eq124097 eq270
    | exact resolve eq270 eq124097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124306 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124122 X0
       have i₂ := eq124097
       grind)
    | exact superpose eq124097 eq124122
    | exact resolve eq124122 eq124097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124097 eq124122
  have eq124316 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq124111
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124111
    | exact resolve eq124111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq124111
  have eq124364 : y = (M.op x y) := by
    first
    | (have i₁ := eq124306 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124306
    | (have j0 := eq124306 y
       grind)
    | exact resolve eq124306 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq124306
  have eq124789 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq124364 eq20
    | exact resolve eq20 eq124364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq124364
  have eq124976 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq124789
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq124789
    | exact resolve eq124789 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq124789
  have eq125221 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq124316 eq270
    | exact resolve eq270 eq124316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq125406 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq124316 eq125221
    | exact resolve eq125221 eq124316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124316 eq125221
  have eq125515 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125406 eq26
    | (have j1 := eq125406 (σ y)
       grind)
    | exact resolve eq26 eq125406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq125406
  have eq125864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq124976 eq125515
    | exact resolve eq125515 eq124976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124976 eq125515
  have eq125932 : False := by grind
  exact eq125932

/-- `Equation2588`: `x = (y ◇ ((z ◇ y) ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxy_pyx_Equation2588 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2588 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2588.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X1)) X0) = X0 := by
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
  have eq53 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X0)) X3) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq14 X3 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq10
    | exact resolve eq10 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq44
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq80 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq50
    | exact resolve eq50 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq81 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq80
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq80
    | exact resolve eq80 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq76 sF2
       grind)
    | exact superpose eq76 eq79
    | exact resolve eq79 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq78
    | exact resolve eq78 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq78
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq103
    | exact resolve eq103 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq432 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq53
    | exact resolve eq53 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq432 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq53 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq53 eq432
    | exact resolve eq432 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq1325 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1264 X0 X1
       have i₂ := eq83 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq83 eq1264
    | exact resolve eq1264 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1264
  have eq1345 : ∀ X0 X1 : G, (M.op (σ (M.op X0 (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1325 X0 X1
       have i₂ := eq53 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have i₁ := eq1325 X0 X1
       have i₂ := eq53 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq53 eq1325
    | exact resolve eq1325 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq38282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq38283 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq38282
    | exact resolve eq38282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38282
  have eq38295 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq38283
       have r₂ := eq28
       grind)
    | exact resolve eq38283 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38283
  have eq38299 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq38295 eq81
    | exact resolve eq81 eq38295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38295
  have eq38391 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq38299
    | exact resolve eq38299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38299
  have eq38392 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38391
  have eq38398 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq82
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq82
    | exact resolve eq82 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38406 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq53 x X0
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq53
    | exact resolve eq53 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq38426 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1345 x X0
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq1345
    | exact resolve eq1345 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345
  have eq38478 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38426 X0
       have i₂ := eq82
       grind)
    | exact superpose eq82 eq38426
    | exact resolve eq38426 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq38426
  have eq38492 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq38398
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38398
    | exact resolve eq38398 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38398
  have eq38718 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq38406 X0
       have i₂ := eq38392
       grind)
    | exact superpose eq38392 eq38406
    | exact resolve eq38406 eq38392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38392 eq38406
  have eq38898 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq38718 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38718
  have eq38941 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq38898 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq38898
    | (have j0 := eq38898 y
       grind)
    | exact resolve eq38898 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38898
  have eq39147 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38941 eq30
    | exact resolve eq30 eq38941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38941
  have eq39270 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq39147
    | exact resolve eq39147 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39147
  have eq39271 : y = (M.op x y) ∨ x = y := by grind
  clear eq39270
  have eq39434 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39271 eq21
    | exact resolve eq21 eq39271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39271
  have eq39555 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39434
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq39434
    | exact resolve eq39434 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39434
  have eq39571 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq39555 eq27
    | exact resolve eq27 eq39555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39555
  have eq59416 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq38492 eq38478
    | exact resolve eq38478 eq38492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38478 eq38492
  have eq59616 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq59416 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59416
  have eq59663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59616 eq39571
    | exact resolve eq39571 eq59616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39571 eq59616
  have eq59829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq59663
  have eq59883 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq59829
       have r₂ := eq28
       grind)
    | exact resolve eq59829 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59829
  have eq59893 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq59883 eq30
    | exact resolve eq30 eq59883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq59883
  have eq60114 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq59893
    | exact resolve eq59893 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq59893
  have eq60115 : x = y := by grind
  clear eq60114
  have eq60130 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq60115
       grind)
    | exact superpose eq60115 eq19
    | exact resolve eq19 eq60115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq60131 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq60115
       grind)
    | exact superpose eq60115 eq25
    | exact resolve eq25 eq60115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq60115
  have eq60275 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq60131
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq60131
    | exact resolve eq60131 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq60131
  have eq60295 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq60275 eq27
    | exact resolve eq27 eq60275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq60275
  have eq60643 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60295 eq81
    | exact resolve eq81 eq60295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq60295
  have eq60743 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq60643
       have i₂ := eq60130
       grind)
    | exact superpose eq60130 eq60643
    | exact resolve eq60643 eq60130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60130 eq60643
  have eq60752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60743 eq15
    | exact resolve eq15 eq60743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60743
  have eq60831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq60752
    | exact resolve eq60752 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq60752
  have eq60852 : False := by grind
  exact eq60852

/-- `Equation2592`: `x = (y ◇ ((z ◇ y) ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_x_pxy_y_pyx_Equation2592 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2592 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2592.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X2)) X0) = X0 := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) x)) X0) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X0) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op (M.op X1 X0) X1) X0
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq985 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq986 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1031 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1062 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq985
       grind)
    | exact superpose eq985 eq39
    | exact resolve eq39 eq985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1063 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1062
    | exact resolve eq1062 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1065 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1063
    | exact resolve eq1063 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1065 eq986
    | exact resolve eq986 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq1065
  have eq1080 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1073
       have r₂ := eq27
       grind)
    | exact resolve eq1073 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1086 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1080 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1080
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1080
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1080
       grind)
    | exact resolve eq13 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080
  have eq1090 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq1086
  have eq1098 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1090 eq152
    | exact resolve eq152 eq1090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq1090
  have eq1101 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1098
    | exact resolve eq1098 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1098
  have eq1104 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1033 y
       grind)
    | (have r₁ := eq1101
       have r₂ := eq1033 y
       grind)
    | exact resolve eq1101 eq1033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1109 : y ≠ y ∨ y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1104
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1104
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1104
       grind)
    | exact resolve eq13 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 : G, (M.op (M.op y (M.op y y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq1104
       grind)
    | exact superpose eq1104 eq16
    | exact resolve eq16 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1109
  have eq1115 : ∀ X0 : G, (M.op (M.op y y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1104 eq1110
    | exact resolve eq1110 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1117 : ∀ X0 : G, (M.op y X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1104 eq1115
    | exact resolve eq1115 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1115
  have eq1120 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1113
       grind)
    | exact superpose eq1113 eq40
    | exact resolve eq40 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1123 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1120
    | exact resolve eq1120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1130 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1117 X0
       grind)
    | exact superpose eq1117 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1117 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1117 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1117 X0
       grind)
    | exact resolve eq13 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1141 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq1154 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1123 eq1033
    | (have j0 := eq1033 (σ y)
       grind)
    | (have r₁ := eq1033 (σ y)
       have r₂ := eq1123
       grind)
    | exact resolve eq1033 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1155 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1154
  have eq1162 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (σ y))) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1155 eq16
    | exact resolve eq16 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1167 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1155 eq1162
    | exact resolve eq1162 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1169 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1155 eq1167
    | exact resolve eq1167 eq1155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1167
  have eq1176 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1169 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1169 X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1169 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1169 X0
       grind)
    | exact resolve eq13 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1187 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1264 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1141 x
       grind)
    | exact superpose eq1141 eq18
    | (have j1 := eq1141 x
       grind)
    | exact resolve eq18 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1312 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1264
       grind)
    | exact superpose eq1264 eq40
    | exact resolve eq40 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1264
  have eq1313 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1312
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1312
    | exact resolve eq1312 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1315 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1313
    | exact resolve eq1313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1455 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1187 eq26
    | (have j1 := eq1187 (σ x)
       grind)
    | exact resolve eq26 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1315 eq1455
    | exact resolve eq1455 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq1455
  have eq1500 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1473
       have r₂ := eq27
       grind)
    | exact resolve eq1473 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1515 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1500 eq188
    | exact resolve eq188 eq1500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq1500
  have eq1541 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1541_12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X1) X0) X2) = X2 := by
      intro X0 X1 X2
      grind
    have f1541_13 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 ∨ y = (M.op x y) := by
      intro X0
      grind
    have f1541_21 : X0 ≠ (M.op (σ x) X0) := by grind
    have f1541_22 : y ≠ (M.op x y) := by grind
    have f1541_23 : ∀ X0 : G, (M.op (M.op (M.op (σ y) (σ x)) (σ y)) X0) = X0 := by
      intro X0
      first
      | (have j0 := f1541_13 X0
         grind)
      | (have r₁ := f1541_13 X0
         have r₂ := f1541_22
         grind)
      | exact resolve f1541_13 f1541_22
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1541_74 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
      intro X0
      first
      | (have i₁ := f1541_12 (σ x) (σ y) X0
         have i₂ := f1541_23 (σ x)
         grind)
      | exact superpose f1541_23 f1541_12
      | exact resolve f1541_12 f1541_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1541_80 : X0 ≠ X0 := by
      first
      | (have i₁ := f1541_21
         have i₂ := f1541_74 X0
         grind)
      | exact superpose f1541_74 f1541_21
      | (have r₁ := f1541_21
         have r₂ := f1541_74 X0
         grind)
      | exact resolve f1541_21 f1541_74
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1541_87 : False := by grind
    exact f1541_87
  clear eq1515
  have eq2005 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1541 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1541 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1541 X0
       grind)
    | exact resolve eq13 eq1541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2023 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2094 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2023 eq1541
    | exact resolve eq1541 eq2023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541 eq2023
  have eq2107 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2094
  have eq2171 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2107 eq141
    | exact resolve eq141 eq2107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq2107
  have eq2174 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2171
    | exact resolve eq2171 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2171
  have eq2179 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1033 x
       have i₂ := eq2174
       grind)
    | exact superpose eq2174 eq1033
    | (have j0 := eq1033 x
       grind)
    | (have r₁ := eq1033 x
       have r₂ := eq2174
       grind)
    | exact resolve eq1033 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq2180 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq2179
  have eq2189 : ∀ X0 : G, (M.op (M.op x (M.op x x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq2180
       grind)
    | exact superpose eq2180 eq16
    | exact resolve eq16 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2193 : ∀ X0 : G, (M.op (M.op x x) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2180 eq2189
    | exact resolve eq2189 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq2197 : ∀ X0 : G, (M.op x X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2180 eq2193
    | exact resolve eq2193 eq2180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180 eq2193
  have eq2206 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2197 y
       grind)
    | exact superpose eq2197 eq18
    | (have j1 := eq2197 y
       grind)
    | exact resolve eq18 eq2197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2197
  have eq2237 : y = (M.op x y) := by grind
  clear eq2206
  have eq2254 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2237
       grind)
    | exact superpose eq2237 eq24
    | exact resolve eq24 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2259 : ∀ X0 : G, (M.op (M.op (M.op (M.op x y) x) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq2237
       grind)
    | exact superpose eq2237 eq183
    | exact resolve eq183 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq2237
  have eq2265 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2254 eq20
    | exact resolve eq20 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2254
  have eq2546 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq2259 eq177
    | exact resolve eq177 eq2259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2259
  have eq2612 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq2546 X0
       grind)
    | exact superpose eq2546 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq2546 X0
       grind)
    | exact resolve eq13 eq2546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2629 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq2612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq2701 : x = (k x x) := by
    first
    | (have i₁ := eq2546 x
       have i₂ := eq2629 x
       grind)
    | exact superpose eq2629 eq2546
    | exact resolve eq2546 eq2629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546 eq2629
  have eq2767 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2701
       grind)
    | exact superpose eq2701 eq39
    | exact resolve eq39 eq2701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2701
  have eq2770 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2767
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2767
    | exact resolve eq2767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2767
  have eq2809 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2770 eq1033
    | (have j0 := eq1033 (σ x)
       grind)
    | (have r₁ := eq1033 (σ x)
       have r₂ := eq2770
       grind)
    | exact resolve eq1033 eq2770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033 eq2770
  have eq2810 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2809
  have eq2882 : ∀ X0 : G, (M.op (M.op (σ x) (M.op (σ x) (σ x))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2810 eq16
    | exact resolve eq16 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2886 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2810 eq2882
    | exact resolve eq2882 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882
  have eq2890 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | exact superpose eq2810 eq2886
    | exact resolve eq2886 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810 eq2886
  have eq2900 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2890 eq26
    | (have j1 := eq2890 (σ y)
       grind)
    | exact resolve eq26 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2890
  have eq2937 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq2900 eq27
    | exact resolve eq27 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2900
  have eq2946 : False := by grind
  exact eq2946
