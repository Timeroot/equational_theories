import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
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
  have eq62 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq69 : x ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq56 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq121
    | exact resolve eq121 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq187 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq629 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq629 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq629 X0 X0
       have r₂ := eq13 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq629 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq629 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq647 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq638 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq638
    | (have j0 := eq638 X0 X1
       grind)
    | exact resolve eq638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq757 : x ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq62 eq69
    | exact resolve eq69 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq69
  have eq858 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
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
  have eq5587 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq187 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq187
    | (have j0 := eq187 x
       grind)
    | exact resolve eq187 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq5621 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5587
  have eq5629 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5621
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5621
    | exact resolve eq5621 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5621
  have eq5646 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5629
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5629 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5629
  have eq5655 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5646 eq50
    | exact resolve eq50 eq5646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq5646
  have eq18034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq123 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18042 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18034
    | exact resolve eq18034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18034
  have eq18053 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq18042
       have r₂ := eq28
       grind)
    | exact resolve eq18042 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18042
  have eq18055 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18053
    | exact resolve eq18053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18053
  have eq18067 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  have eq18074 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18055 eq59
    | exact resolve eq59 eq18055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18055
  have eq18116 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18074
    | exact resolve eq18074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18074
  have eq18118 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq18067
    | exact resolve eq18067 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18067
  have eq18119 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq18118
  have eq18131 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18116
  have eq18181 : x = (M.op x y) ∨ y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18131
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18131
    | exact resolve eq18131 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18131
  have eq18182 : y = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18181
  have eq18267 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18182
       grind)
    | exact superpose eq18182 eq110
    | exact resolve eq110 eq18182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq18182
  have eq18294 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18267
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18267
    | exact resolve eq18267 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18267
  have eq18403 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18294 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq18294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18294
  have eq18413 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18403
    | exact resolve eq18403 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18403
  have eq18414 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18413
  have eq18426 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq18414
    | exact resolve eq18414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18414
  have eq18427 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18426
  have eq18447 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18427 eq59
    | exact resolve eq59 eq18427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18427
  have eq18489 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18447
    | exact resolve eq18447 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18447
  have eq18490 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18489
  have eq18500 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18490 eq28
    | exact resolve eq28 eq18490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18490
  have eq19753 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18119 eq123
    | exact resolve eq123 eq18119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq18119
  have eq19768 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19753
  have eq19776 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19768
       have r₂ := eq18500
       grind)
    | exact resolve eq19768 eq18500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19768
  have eq19791 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq19776
       grind)
    | exact superpose eq19776 eq59
    | exact resolve eq59 eq19776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq19776
  have eq19833 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19791
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19791
    | exact resolve eq19791 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19791
  have eq19841 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19833 eq57
    | exact resolve eq57 eq19833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19833
  have eq19997 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19841 eq5655
    | exact resolve eq5655 eq19841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq19841
  have eq20088 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq19997
    | exact resolve eq19997 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19997
  have eq21002 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq20088
       grind)
    | exact superpose eq20088 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq20088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20088
  have eq21019 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq21002
  have eq21063 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq858 x
       have i₂ := eq21019
       grind)
    | exact superpose eq21019 eq858
    | exact resolve eq858 eq21019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21019
  have eq21140 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56 eq21063
    | exact resolve eq21063 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21063
  have eq21151 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21140
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21140
    | exact resolve eq21140 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21140
  have eq21152 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21151
  have eq21163 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21152 eq21
    | exact resolve eq21 eq21152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21152
  have eq21291 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21163
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21163
    | exact resolve eq21163 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21163
  have eq21410 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21291 eq18500
    | (have r₁ := eq18500
       have r₂ := eq21291
       grind)
    | exact resolve eq18500 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18500
  have eq21432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21410
  have eq21433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21432
  have eq21512 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21433 eq57
    | exact resolve eq57 eq21433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21433
  have eq21685 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21512 eq862
    | exact resolve eq862 eq21512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq21512
  have eq21765 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq57 eq21685
    | exact resolve eq21685 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq21685
  have eq21783 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq21765
    | exact resolve eq21765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21765
  have eq21796 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21783 eq28
    | exact resolve eq28 eq21783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21783
  have eq21836 : x = (M.op x y) := by
    first
    | (have r₁ := eq21796
       have r₂ := eq21291
       grind)
    | exact resolve eq21796 eq21291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21291 eq21796
  have eq21840 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq21836 eq21
    | exact resolve eq21 eq21836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq21843 : x = (M.op x x) := by
    first
    | exact superpose eq21836 eq56
    | exact resolve eq56 eq21836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21904 : x ≠ x ∨ x = (k x x) := by
    first
    | exact superpose eq21836 eq757
    | (have r₁ := eq757
       have r₂ := eq21836
       grind)
    | exact resolve eq757 eq21836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq21915 : x = (k x x) := by grind
  clear eq21904
  have eq21982 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21840
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21840
    | exact resolve eq21840 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21840
  have eq22021 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq21982 eq27
    | exact resolve eq27 eq21982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22212 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq858 x
       have i₂ := eq21843
       grind)
    | exact superpose eq21843 eq858
    | exact resolve eq858 eq21843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq858 eq21843
  have eq22284 : y = (M.op x y) := by
    first
    | exact superpose eq56 eq22212
    | exact resolve eq22212 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq22212
  have eq22295 : y = (M.op x y) := by
    first
    | (have i₁ := eq22284
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22284
    | exact resolve eq22284 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22284
  have eq22301 : x = y := by
    first
    | exact superpose eq21836 eq22295
    | exact resolve eq22295 eq21836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21836 eq22295
  have eq22309 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22301
       grind)
    | exact superpose eq22301 eq25
    | exact resolve eq25 eq22301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22301
  have eq22435 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22309
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22309
    | exact resolve eq22309 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22309
  have eq22489 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21982 eq22435
    | exact resolve eq22435 eq21982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22435
  have eq22823 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq647 x x
       have i₂ := eq21915
       grind)
    | exact superpose eq21915 eq647
    | (have j0 := eq647 x x
       grind)
    | exact resolve eq647 eq21915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq21915
  have eq22826 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22823
  have eq22827 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22826
  have eq22840 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq22827
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22827
    | exact resolve eq22827 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22827
  have eq22855 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21982 eq22840
    | exact resolve eq22840 eq21982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21982 eq22840
  have eq23201 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22489 eq22021
    | exact resolve eq22021 eq22489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22021 eq22489
  have eq23732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22855 eq23201
    | exact resolve eq23201 eq22855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22855 eq23201
  have eq23733 : False := by grind
  exact eq23733

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_pyy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
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
  have eq34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (M.op X0 X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq34
    | exact resolve eq34 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq9
    | exact resolve eq9 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq29
    | exact resolve eq29 eq18
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
  have eq101 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq39 X1 X2 X0
       grind)
    | exact superpose eq39 eq34
    | exact resolve eq34 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X1) (σ X0)
       have i₂ := eq75 X1 X0
       grind)
    | exact superpose eq75 eq34
    | (have j1 := eq75 X1 X0
       grind)
    | exact resolve eq34 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq214 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq215 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq214 X0
       have j1 := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq214 X0
       have r₂ := eq12 (σ (k X0 X0)) (σ X0)
       grind)
    | (have r₁ := eq214 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq218 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq215
    | (have j0 := eq215 X0
       grind)
    | exact resolve eq215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq582 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq218 (τ X0)
       grind)
    | exact superpose eq218 eq19
    | (have j1 := eq218 (τ X0)
       grind)
    | exact resolve eq19 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq620 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq582
    | (have j0 := eq582 X0
       grind)
    | exact resolve eq582 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq626 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq620 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq620
    | (have j0 := eq620 X0
       grind)
    | exact resolve eq620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq631 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq626 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq626
    | (have j0 := eq626 X0
       grind)
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq634 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq631 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq631
    | (have j0 := eq631 X0
       have j1 := eq14 X0 X0
       grind)
    | exact resolve eq631 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq670 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq653 X0
       have j1 := eq46 X0 X0
       grind)
    | (have r₁ := eq653 x
       have r₂ := eq46 x x
       grind)
    | exact resolve eq653 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq734 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (M.op X1 (τ X0)) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq29
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq29 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq77
  have eq741 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op X1 (τ X0)) (τ X2)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq734 X0 X1 X2
       have i₂ := eq61 X0 X1 X2
       grind)
    | exact superpose eq61 eq734
    | (have j0 := eq734 X0 X1 X2
       grind)
    | exact resolve eq734 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq734
  have eq1984 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq203 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq1985 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1984 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq2046 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (σ X0) (σ X0) X1
       have i₂ := eq1985 X0
       grind)
    | exact superpose eq1985 eq39
    | (have j1 := eq1985 X0
       grind)
    | exact resolve eq39 eq1985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1985
  have eq2088 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2046 X0 X1
       have i₂ := eq34 (σ X0) X1
       grind)
    | exact superpose eq34 eq2046
    | (have j0 := eq2046 X0 X1
       grind)
    | exact resolve eq2046 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq2872 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) X2) = (k (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (k (σ X1) X2) (σ X0)
       have i₂ := eq197 X1 X2 X0
       grind)
    | exact superpose eq197 eq12
    | (have j0 := eq12 (k (σ X1) X2) (σ X0)
       have j1 := eq197 X1 X2 X0
       grind)
    | (have r₁ := eq12 (k (σ X0) X1) (σ X2)
       have r₂ := eq197 X0 X1 X2
       grind)
    | exact resolve eq12 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2879 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ X0) X1) (σ X0)) X1) = X1 ∨ (M.op (σ X0) (σ X0)) = (k (σ X2) X3) ∨ (M.op (σ X0) (k (σ X2) X3)) = (σ (k (k X2 (τ X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq39 (σ X0) (k (σ X2) X3) X1
       have i₂ := eq197 X2 X3 X0
       grind)
    | exact superpose eq197 eq39
    | (have j1 := eq197 X2 X3 X0
       grind)
    | exact resolve eq39 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq197
  have eq2910 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (k (k (σ X1) X2) (σ X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2872 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2939 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X2) X3)) = (σ (k (k X2 (τ X3)) X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X2) X3) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2879 X0 X1 X2 X3
       have i₂ := eq34 (σ X0) X1
       grind)
    | exact superpose eq34 eq2879
    | (have j0 := eq2879 X0 X1 X2 X3
       grind)
    | exact resolve eq2879 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq2944 : ∀ X0 X1 X2 : G, (k (σ X1) X2) = (σ (k (k X1 (τ X2)) X0)) ∨ (k (σ X1) X2) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2910 X0 X1 X2
       have i₂ := eq28 X1 X2 X0
       grind)
    | exact superpose eq28 eq2910
    | (have j0 := eq2910 X0 X1 X2
       grind)
    | exact resolve eq2910 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2910
  have eq3847 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2088 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2088
    | (have j0 := eq2088 (k (τ X0) (τ X0)) X0
       grind)
    | exact resolve eq2088 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq3911 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3847 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3847
    | (have j0 := eq3847 (k (σ (τ X0)) X0) X0
       grind)
    | exact resolve eq3847 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3847
  have eq3915 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3911 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3911
    | (have j0 := eq3911 (k X0 X0) X0
       grind)
    | exact resolve eq3911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911
  have eq3932 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X0) X0
       have i₂ := eq3915 X0 X1
       grind)
    | exact superpose eq3915 eq34
    | (have j1 := eq3915 X0 (k X0 X0)
       grind)
    | exact resolve eq34 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq4113 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3932 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3932
  have eq4114 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq4113 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq4129 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4114 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq4114
    | exact resolve eq4114 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4136 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq34 X0 (k X0 X0)
       have i₂ := eq4114 X0
       grind)
    | exact superpose eq4114 eq34
    | exact resolve eq34 eq4114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq4147 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 X0)) = (M.op X1 (M.op (M.op X0 X1) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X0 (k X0 X0)
       have i₂ := eq4114 X0
       grind)
    | exact superpose eq4114 eq101
    | exact resolve eq101 eq4114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq4114
  have eq4407 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4136 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4136
    | exact resolve eq4136 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4136
  have eq4505 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq46 (σ (k X0 X0)) (σ X0)
       have i₂ := eq4407 X0
       grind)
    | exact superpose eq4407 eq46
    | exact resolve eq46 eq4407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4538 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4505 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq4505
    | (have j0 := eq4505 X0
       grind)
    | exact resolve eq4505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4505
  have eq28968 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq631 (τ X0)
       have i₂ := eq741 X0 (τ X0) X0
       grind)
    | exact superpose eq741 eq631
    | (have j0 := eq631 (τ X0)
       have j1 := eq741 X0 (τ X0) x
       grind)
    | exact resolve eq631 eq741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq741
  have eq29003 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq28968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28968
  have eq29040 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29003 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq29003
    | (have j0 := eq29003 X0
       grind)
    | exact resolve eq29003 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29003
  have eq29072 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29040 X0
       have i₂ := eq670 (τ X0)
       grind)
    | exact superpose eq670 eq29040
    | (have j0 := eq29040 X0
       grind)
    | exact resolve eq29040 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq29040
  have eq29836 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 (τ X0) (τ X0)
       have i₂ := eq29072 X0
       grind)
    | exact superpose eq29072 eq46
    | (have j1 := eq29072 X0
       grind)
    | (have r₁ := eq46 (τ X0) (τ X0)
       have r₂ := eq29072 X0
       grind)
    | exact resolve eq46 eq29072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq29907 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq29072 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29072
  have eq29908 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq29836 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29836
  have eq29933 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29908 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq29908
    | (have j0 := eq29908 X0
       grind)
    | exact resolve eq29908 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29908
  have eq29963 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq29933 X0
       have j1 := eq29907 X0
       grind)
    | (have r₁ := eq29933 X0
       have r₂ := eq29907 X0
       grind)
    | exact resolve eq29933 eq29907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29907 eq29933
  have eq30291 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29963 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq29963
    | exact resolve eq29963 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30487 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq30291 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq30291
    | exact resolve eq30291 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30291
  have eq30518 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30487 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30487
    | exact resolve eq30487 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30487
  have eq30592 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4129 X0
       have i₂ := eq30518 X0
       grind)
    | exact superpose eq30518 eq4129
    | exact resolve eq4129 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq30605 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4407 X0
       have i₂ := eq30518 X0
       grind)
    | exact superpose eq30518 eq4407
    | exact resolve eq4407 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407
  have eq30614 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4538 X0
       have i₂ := eq30518 X0
       grind)
    | exact superpose eq30518 eq4538
    | exact resolve eq4538 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4538
  have eq30673 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq30518 (σ X0)
       grind)
    | exact superpose eq30518 eq15
    | exact resolve eq15 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30744 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30673 X0
       have i₂ := eq30518 X0
       grind)
    | exact superpose eq30518 eq30673
    | exact resolve eq30673 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30673
  have eq31721 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (k (σ X0) (σ X0))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (k (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq4147 (σ X0) (σ X0)
       have i₂ := eq30744 X0
       grind)
    | exact superpose eq30744 eq4147
    | exact resolve eq4147 eq30744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147
  have eq31745 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (k X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq31721 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq31721
    | exact resolve eq31721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31721
  have eq31795 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq31745 X0
       have i₂ := eq30518 X0
       grind)
    | exact superpose eq30518 eq31745
    | exact resolve eq31745 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31745
  have eq31821 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq31795 X0
       have i₂ := eq30744 (M.op X0 X0)
       grind)
    | exact superpose eq30744 eq31795
    | exact resolve eq31795 eq30744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31795
  have eq32865 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 (M.op X0 X0) X0
       have i₂ := eq30605 X0
       grind)
    | exact superpose eq30605 eq75
    | (have j0 := eq75 (M.op X0 X0) X0
       grind)
    | exact resolve eq75 eq30605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq30605
  have eq32972 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq32865 X0
       have j1 := eq30614 X0
       grind)
    | (have r₁ := eq32865 X0
       have r₂ := eq30614 X0
       grind)
    | exact resolve eq32865 eq30614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32865
  have eq33011 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq32972 X0
       have i₂ := eq30744 (M.op X0 X0)
       grind)
    | exact superpose eq30744 eq32972
    | (have j0 := eq32972 X0
       grind)
    | exact resolve eq32972 eq30744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32972
  have eq219591 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2944 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2944
  have eq219594 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq219591 X0 X1 X2
       have j1 := eq2939 X2 X1 X0 X1
       grind)
    | (have r₁ := eq219591 X0 X1 X0
       have r₂ := eq2939 X0 (k (σ X0) X1) X2 x
       grind)
    | exact resolve eq219591 eq2939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939 eq219591
  have eq219947 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq219594 X0 X1 X2
       have i₂ := eq30744 X2
       grind)
    | exact superpose eq30744 eq219594
    | (have j0 := eq219594 X0 X1 X2
       grind)
    | exact resolve eq219594 eq30744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219594
  have eq318837 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq31821 X0
       have i₂ := eq33011 X0
       grind)
    | exact superpose eq33011 eq31821
    | (have j1 := eq33011 X0
       grind)
    | exact resolve eq31821 eq33011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31821 eq33011
  have eq319296 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq318837 X0
       have i₂ := eq30744 X0
       grind)
    | exact superpose eq30744 eq318837
    | (have j0 := eq318837 X0
       grind)
    | exact resolve eq318837 eq30744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30744 eq318837
  have eq319354 : ∀ X0 : G, (σ X0) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq319296 X0
       have j1 := eq30614 X0
       grind)
    | (have r₁ := eq319296 X0
       have r₂ := eq30614 X0
       grind)
    | exact resolve eq319296 eq30614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30614 eq319296
  have eq321331 : ∀ X0 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 (M.op X0 X0))
       have i₂ := eq319354 X0
       grind)
    | exact superpose eq319354 eq10
    | exact resolve eq10 eq319354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321332 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (M.op X0 X0)) X1
       have i₂ := eq319354 X0
       grind)
    | exact superpose eq319354 eq15
    | exact resolve eq15 eq319354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319354
  have eq321733 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k X0 (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq321332 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq321332
    | exact resolve eq321332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321332
  have eq321734 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq321331 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq321331
    | exact resolve eq321331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321331
  have eq1701435 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (σ X2) (k (σ (τ X0)) X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq219947 (τ X0) X1 X2
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq219947
    | (have j0 := eq219947 (τ X0) X1 X2
       grind)
    | exact resolve eq219947 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq219947
  have eq1703093 : ∀ X0 X1 X2 : G, (σ (k (τ (k X0 X1)) X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1701435 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1701435
    | (have j0 := eq1701435 X0 X1 X2
       grind)
    | exact resolve eq1701435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701435
  have eq1703445 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k (σ (τ X0)) X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1703093 X0 X1 X2
       have i₂ := eq18 (k X0 X1) X2
       grind)
    | exact superpose eq18 eq1703093
    | (have j0 := eq1703093 X0 X1 X2
       grind)
    | exact resolve eq1703093 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1703093
  have eq1703693 : ∀ X0 X1 X2 : G, (k (k X0 X1) (σ X2)) = (M.op (σ X2) (k X0 X1)) ∨ (k X0 X1) = (σ (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1703445 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1703445
    | (have j0 := eq1703445 X0 X1 X2
       grind)
    | exact resolve eq1703445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703445
  have eq1938866 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1703693 X0 (M.op X0 X0) x
       have i₂ := eq321734 X0
       grind)
    | exact superpose eq321734 eq1703693
    | exact resolve eq1703693 eq321734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703693
  have eq1940473 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1938866 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1938866
    | (have j0 := eq1938866 X1 (τ X0)
       grind)
    | exact resolve eq1938866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1941301 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1938866 (σ X1) X0
       grind)
    | exact superpose eq1938866 eq15
    | (have j1 := eq1938866 (σ X1) X0
       grind)
    | exact resolve eq15 eq1938866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938866
  have eq1942127 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1940473 X0 X1
       have i₂ := eq29963 X0
       grind)
    | exact superpose eq29963 eq1940473
    | (have j0 := eq1940473 X0 X1
       grind)
    | exact resolve eq1940473 eq29963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29963 eq1940473
  have eq1942458 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1942127 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq1942127
    | (have j0 := eq1942127 X0 X1
       grind)
    | exact resolve eq1942127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942127
  have eq1942634 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1942458 X0 X1
       have i₂ := eq30518 X0
       grind)
    | exact superpose eq30518 eq1942458
    | (have j0 := eq1942458 X0 X1
       grind)
    | exact resolve eq1942458 eq30518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30518 eq1942458
  have eq1950360 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 (k X1 (M.op X1 X1)))) ∨ (M.op X0 X0) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq321733 X1 X0
       have i₂ := eq1942634 X0 (k X1 (M.op X1 X1))
       grind)
    | exact superpose eq1942634 eq321733
    | (have j1 := eq1942634 X0 (k X1 (M.op X1 X1))
       grind)
    | exact resolve eq321733 eq1942634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321733 eq1942634
  have eq1950799 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1950360 X0 X1
       have i₂ := eq321734 X1
       grind)
    | exact superpose eq321734 eq1950360
    | (have j0 := eq1950360 X0 X1
       grind)
    | exact resolve eq1950360 eq321734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950360
  have eq1951383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1950799 X0 X1
       have i₂ := eq321734 X1
       grind)
    | exact superpose eq321734 eq1950799
    | (have j0 := eq1950799 X0 X1
       grind)
    | exact resolve eq1950799 eq321734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321734 eq1950799
  have eq2068042 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1941301 x y
       grind)
    | exact superpose eq1941301 eq16
    | (have j1 := eq1941301 x y
       grind)
    | exact resolve eq16 eq1941301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941301
  have eq2073205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2068042
       have i₂ := eq1951383 x y
       grind)
    | exact superpose eq1951383 eq2068042
    | (have j1 := eq1951383 x y
       grind)
    | (have r₁ := eq2068042
       have r₂ := eq1951383 x y
       grind)
    | exact resolve eq2068042 eq1951383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951383 eq2068042
  have eq2073212 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq2073205
  have eq2073364 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2073212
       grind)
    | exact superpose eq2073212 eq10
    | exact resolve eq10 eq2073212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073212
  have eq2074387 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2073364
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2073364
    | exact resolve eq2073364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073364
  have eq2074388 : y = (M.op x x) := by grind
  clear eq2074387
  have eq2077290 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30592 x
       have i₂ := eq2074388
       grind)
    | exact superpose eq2074388 eq30592
    | exact resolve eq30592 eq2074388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30592
  have eq2077520 : y = (M.op x y) := by
    first
    | (have i₁ := eq37 x x
       have i₂ := eq2074388
       grind)
    | exact superpose eq2074388 eq37
    | exact resolve eq37 eq2074388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2074388
  have eq2086278 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2077290
       grind)
    | exact superpose eq2077290 eq16
    | exact resolve eq16 eq2077290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077290
  have eq2087068 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2086278
       have i₂ := eq2077520
       grind)
    | exact superpose eq2077520 eq2086278
    | exact resolve eq2086278 eq2077520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077520 eq2086278
  have eq2087069 : False := by grind
  exact eq2087069

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  clear eq55
  have eq82 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq93 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq50
    | exact resolve eq50 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq94 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq93
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq93
    | exact resolve eq93 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq93
  have eq118 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq118
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq127
    | exact resolve eq127 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq133
    | exact resolve eq133 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq134
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq134
    | exact resolve eq134 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq1070 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
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
  have eq1187 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq135 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq1188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1187
    | exact resolve eq1187 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1191 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1188
       have r₂ := eq28
       grind)
    | exact resolve eq1188 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1191
    | exact resolve eq1191 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1197 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1193 eq57
    | exact resolve eq57 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1197 eq1074
    | exact resolve eq1074 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1197
  have eq1256 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57 eq1235
    | exact resolve eq1235 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1235
  have eq1260 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1256
    | exact resolve eq1256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1323 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1260 eq1193
    | exact resolve eq1193 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq1260
  have eq1324 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1323
  have eq1328 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1324 eq30
    | exact resolve eq30 eq1324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1324
  have eq1349 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1328
    | exact resolve eq1328 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1328
  have eq1350 : x = (M.op x y) ∨ x = y := by grind
  clear eq1349
  have eq1356 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1350 eq56
    | exact resolve eq56 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1456 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq1070 x
       have i₂ := eq1356
       grind)
    | exact superpose eq1356 eq1070
    | exact resolve eq1070 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq1356
  have eq1478 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56 eq1456
    | exact resolve eq1456 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1456
  have eq1482 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1478
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1478
    | exact resolve eq1478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq1508 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1482 eq1350
    | exact resolve eq1350 eq1482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq1482
  have eq1509 : x = y := by grind
  clear eq1508
  have eq1582 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1509
       grind)
    | exact superpose eq1509 eq19
    | exact resolve eq19 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1583 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1509
       grind)
    | exact superpose eq1509 eq25
    | exact resolve eq25 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1509
  have eq1603 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1583
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1583
    | exact resolve eq1583 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1583
  have eq1606 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1603 eq27
    | exact resolve eq27 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1603
  have eq1752 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1606 eq94
    | exact resolve eq94 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1606
  have eq1772 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1752
       have i₂ := eq1582
       grind)
    | exact superpose eq1582 eq1752
    | exact resolve eq1752 eq1582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1582 eq1752
  have eq1776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1772 eq15
    | exact resolve eq15 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1803 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1776
    | exact resolve eq1776 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1776
  have eq1808 : False := by grind
  exact eq1808

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq55
  have eq84 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq95 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq84 sF2
       grind)
    | exact superpose eq84 eq50
    | exact resolve eq50 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq96 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq95
       have i₂ := eq84 x
       grind)
    | exact superpose eq84 eq95
    | exact resolve eq95 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq95
  have eq120 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq120
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq129
    | exact resolve eq129 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq136 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq135
    | exact resolve eq135 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq136
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq136
    | exact resolve eq136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1090 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
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
  have eq1234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq137 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1234
    | exact resolve eq1234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1238 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1235
       have r₂ := eq28
       grind)
    | exact resolve eq1235 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1238
    | exact resolve eq1238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1244 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1240 eq57
    | exact resolve eq57 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1244 eq1094
    | exact resolve eq1094 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1244
  have eq1334 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57 eq1312
    | exact resolve eq1312 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1312
  have eq1338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1334
    | exact resolve eq1334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1352 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1338 eq1240
    | exact resolve eq1240 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240 eq1338
  have eq1353 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1352
  have eq1388 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1353 eq30
    | exact resolve eq30 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1353
  have eq1409 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1388
    | exact resolve eq1388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1388
  have eq1410 : x = (M.op x y) ∨ x = y := by grind
  clear eq1409
  have eq1416 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1410 eq56
    | exact resolve eq56 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq1090 x
       have i₂ := eq1416
       grind)
    | exact superpose eq1416 eq1090
    | exact resolve eq1090 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1416
  have eq1571 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56 eq1548
    | exact resolve eq1548 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1548
  have eq1575 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1571
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1571
    | exact resolve eq1571 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1601 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1575 eq1410
    | exact resolve eq1410 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq1575
  have eq1602 : x = y := by grind
  clear eq1601
  have eq1618 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1602
       grind)
    | exact superpose eq1602 eq19
    | exact resolve eq19 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1619 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1602
       grind)
    | exact superpose eq1602 eq25
    | exact resolve eq25 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1602
  have eq1639 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1619
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1619
    | exact resolve eq1619 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1619
  have eq1722 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1639 eq27
    | exact resolve eq27 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1639
  have eq1779 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1722 eq96
    | exact resolve eq96 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1722
  have eq1800 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1779
       have i₂ := eq1618
       grind)
    | exact superpose eq1618 eq1779
    | exact resolve eq1779 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq1779
  have eq1804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1800 eq15
    | exact resolve eq15 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1804
    | exact resolve eq1804 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1804
  have eq1836 : False := by grind
  exact eq1836

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxy_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq55
  have eq84 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq95 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq84 sF2
       grind)
    | exact superpose eq84 eq50
    | exact resolve eq50 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq96 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq95
       have i₂ := eq84 x
       grind)
    | exact superpose eq84 eq95
    | exact resolve eq95 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq95
  have eq120 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq120
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq129
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq129
    | exact resolve eq129 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq136 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq135
    | exact resolve eq135 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq136
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq136
    | exact resolve eq136 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq1090 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61
    | (have j0 := eq61 x X0 y
       grind)
    | exact resolve eq61 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1094 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
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
  have eq1234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq137 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq1235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1234
    | exact resolve eq1234 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1238 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1235
       have r₂ := eq28
       grind)
    | exact resolve eq1235 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1240 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1238
    | exact resolve eq1238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1244 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1240 eq57
    | exact resolve eq57 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1312 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1244 eq1094
    | exact resolve eq1094 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1244
  have eq1334 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq57 eq1312
    | exact resolve eq1312 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1312
  have eq1338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1334
    | exact resolve eq1334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1352 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1338 eq1240
    | exact resolve eq1240 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240 eq1338
  have eq1353 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1352
  have eq1388 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1353 eq30
    | exact resolve eq30 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1353
  have eq1409 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1388
    | exact resolve eq1388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1388
  have eq1410 : x = (M.op x y) ∨ x = y := by grind
  clear eq1409
  have eq1416 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1410 eq56
    | exact resolve eq56 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : y = (M.op (M.op (M.op x y) x) y) ∨ x = y := by
    first
    | (have i₁ := eq1090 x
       have i₂ := eq1416
       grind)
    | exact superpose eq1416 eq1090
    | exact resolve eq1090 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1416
  have eq1571 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq56 eq1548
    | exact resolve eq1548 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1548
  have eq1575 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1571
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1571
    | exact resolve eq1571 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571
  have eq1601 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1575 eq1410
    | exact resolve eq1410 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq1575
  have eq1602 : x = y := by grind
  clear eq1601
  have eq1618 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1602
       grind)
    | exact superpose eq1602 eq19
    | exact resolve eq19 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1619 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1602
       grind)
    | exact superpose eq1602 eq25
    | exact resolve eq25 eq1602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1602
  have eq1639 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1619
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1619
    | exact resolve eq1619 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1619
  have eq1722 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1639 eq27
    | exact resolve eq27 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1639
  have eq1779 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1722 eq96
    | exact resolve eq96 eq1722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1722
  have eq1800 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1779
       have i₂ := eq1618
       grind)
    | exact superpose eq1618 eq1779
    | exact resolve eq1779 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq1779
  have eq1804 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1800 eq15
    | exact resolve eq15 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1804
    | exact resolve eq1804 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1804
  have eq1836 : False := by grind
  exact eq1836

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq22
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
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq81 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq110 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
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
  have eq149 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq163 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq149 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq149
    | (have j0 := eq149 X0
       grind)
    | exact resolve eq149 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq149
  have eq164 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq163 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq163
    | (have j0 := eq163 X0
       grind)
    | exact resolve eq163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq165 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq164 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq164 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq164 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq168 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq165 (σ X0)
       grind)
    | exact superpose eq165 eq15
    | exact resolve eq15 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq168 X0
       have i₂ := eq165 X0
       grind)
    | exact superpose eq165 eq168
    | exact resolve eq168 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq201 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) (σ X0) X1
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq26
    | exact resolve eq26 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1663 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (M.op (τ X1) X1) X1
       have i₂ := eq22 (τ X1) X1
       grind)
    | exact superpose eq22 eq81
    | (have j0 := eq81 (M.op (τ X0) X1) X0
       grind)
    | exact resolve eq81 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq1694 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) X1))) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1663 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663
  have eq1713 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) X1))) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1694 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1694
    | (have j0 := eq1694 X0 X1
       grind)
    | exact resolve eq1694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq2562 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq278
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq278
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq278
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq278
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2563 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2562
  have eq5020 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (τ (σ X0)) X1)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ (M.op (τ (σ X0)) X1))
       have i₂ := eq1713 (σ X0) X1
       grind)
    | exact superpose eq1713 eq45
    | (have j1 := eq1713 (σ X0) X1
       grind)
    | exact resolve eq45 eq1713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1713
  have eq5038 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op (τ (σ X0)) X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5020 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) X1)
       grind)
    | exact superpose eq10 eq5020
    | (have j0 := eq5020 X0 X1
       grind)
    | exact resolve eq5020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5020
  have eq5065 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5038 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5038
    | (have j0 := eq5038 X0 X1
       grind)
    | exact resolve eq5038 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5038
  have eq5078 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5065 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5065
    | (have j0 := eq5065 X0 X1
       grind)
    | exact resolve eq5065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5065
  have eq5085 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5078 X0 X1
       have j1 := eq34 X0 X1
       grind)
    | (have r₁ := eq5078 X0 X1
       have r₂ := eq34 X0 X1
       grind)
    | exact resolve eq5078 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq5078
  have eq5093 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5085 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq5085
    | exact resolve eq5085 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5085
  have eq5396 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5093 (M.op (M.op X0 X2) (M.op X0 X1)) X2
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq5093
    | exact resolve eq5093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5444 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (M.op (σ X0) X1) X0
       have i₂ := eq5093 (σ X0) X1
       grind)
    | exact superpose eq5093 eq39
    | exact resolve eq39 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq5093
  have eq27740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2563
       grind)
    | exact superpose eq2563 eq16
    | exact resolve eq16 eq2563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq27741 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq27740
       have r₂ := eq179 x
       grind)
    | exact resolve eq27740 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27740
  have eq61976 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24 x y
       have i₂ := eq27741
       grind)
    | exact superpose eq27741 eq24
    | exact resolve eq24 eq27741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27741
  have eq64108 : y = (τ (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq61976
       grind)
    | exact superpose eq61976 eq10
    | exact resolve eq10 eq61976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61976
  have eq64279 : x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64108
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64108
    | exact resolve eq64108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64108
  have eq64286 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64279
       grind)
    | exact superpose eq64279 eq16
    | exact resolve eq16 eq64279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64279
  have eq64287 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq64286
       have r₂ := eq179 x
       grind)
    | exact resolve eq64286 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64286
  have eq65232 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5444 x (σ y)
       have i₂ := eq64287
       grind)
    | exact superpose eq64287 eq5444
    | exact resolve eq5444 eq64287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5444 eq64287
  have eq65511 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65232
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq65232
    | exact resolve eq65232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65232
  have eq65546 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65511
       have i₂ := eq165 x
       grind)
    | exact superpose eq165 eq65511
    | exact resolve eq65511 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq65511
  have eq65547 : x = (M.op x x) := by grind
  clear eq65546
  have eq65556 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq201 x X0
       have i₂ := eq65547
       grind)
    | exact superpose eq65547 eq201
    | exact resolve eq201 eq65547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq65680 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26 x x X0
       have i₂ := eq65547
       grind)
    | exact superpose eq65547 eq26
    | exact resolve eq26 eq65547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq65690 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op X0 (M.op (M.op x X0) x)) := by
    intro X0
    first
    | (have i₁ := eq110 X0 x x
       have i₂ := eq65547
       grind)
    | exact superpose eq65547 eq110
    | exact resolve eq110 eq65547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq65769 : ∀ X0 : G, (k X0 (M.op (M.op x X0) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5396 X0 x x
       have i₂ := eq65547
       grind)
    | exact superpose eq65547 eq5396
    | exact resolve eq5396 eq65547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396 eq65547
  have eq65830 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq65769 X0
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq65769
    | exact resolve eq65769 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65769
  have eq65862 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq65690 x
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq65690
    | exact resolve eq65690 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65690
  have eq65869 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65680 X0
       have i₂ := eq22 x X0
       grind)
    | exact superpose eq22 eq65680
    | exact resolve eq65680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65680
  have eq65960 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65556 X0
       have i₂ := eq22 (σ x) X0
       grind)
    | exact superpose eq22 eq65556
    | exact resolve eq65556 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq65556
  have eq66727 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq278
       have i₂ := eq65830 y
       grind)
    | exact superpose eq65830 eq278
    | exact resolve eq278 eq65830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq65830
  have eq66733 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66727
       have i₂ := eq65869 y
       grind)
    | exact superpose eq65869 eq66727
    | exact resolve eq66727 eq65869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66727
  have eq66734 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66733
  have eq66766 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66734
       have i₂ := eq65960 (σ y)
       grind)
    | exact superpose eq65960 eq66734
    | exact resolve eq66734 eq65960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65960 eq66734
  have eq66767 : (σ x) = (σ y) := by grind
  clear eq66766
  have eq68528 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66767
       grind)
    | exact superpose eq66767 eq16
    | exact resolve eq16 eq66767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68742 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq68528
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq68528
    | exact resolve eq68528 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq68528
  have eq68773 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq68742
       have i₂ := eq65862 x
       grind)
    | exact superpose eq65862 eq68742
    | exact resolve eq68742 eq65862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65862 eq68742
  have eq68797 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq68773
       have i₂ := eq65869 y
       grind)
    | exact superpose eq65869 eq68773
    | exact resolve eq68773 eq65869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65869 eq68773
  have eq68808 : False := by grind
  exact eq68808

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyy_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X2) X0) X1) X0) = X0 := by
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
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq16 (M.op X0 X1) X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq178 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq178
    | (have j0 := eq178 x y
       grind)
    | exact resolve eq178 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq178 (M.op X0 X1) X0
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X0 X1) X0
       have i₂ := eq178 X0 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq205 : (σ (M.op y y)) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq179 y
       grind)
    | exact superpose eq179 eq40
    | exact resolve eq40 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq253 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq179 sF2
       grind)
    | exact superpose eq179 eq141
    | exact resolve eq141 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq274 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq179 sF3
       grind)
    | exact superpose eq179 eq152
    | exact resolve eq152 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq686 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (k X0 (M.op (M.op X0 X1) X2)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op (M.op X0 X1) X2)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : (M.op x y) = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq713 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq722 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq722 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq746 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq723 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq723
    | (have j0 := eq723 (σ X0)
       grind)
    | exact resolve eq723 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1487 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq703
       grind)
    | exact superpose eq703 eq39
    | exact resolve eq39 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1488 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1487
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1487
    | exact resolve eq1487 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq1490 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1488
    | exact resolve eq1488 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq6673 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq686 X0 x X0
       have i₂ := eq178 X0 x
       grind)
    | exact superpose eq178 eq686
    | (have j0 := eq686 X0 x x
       grind)
    | exact resolve eq686 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq6744 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6673 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq6759 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 (k X0 X0) X0
       have i₂ := eq6744 X0
       grind)
    | exact superpose eq6744 eq178
    | (have j1 := eq6744 X0
       grind)
    | exact resolve eq178 eq6744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6744
  have eq17615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1490 eq713
    | exact resolve eq713 eq1490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1490
  have eq17623 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17615
       have r₂ := eq27
       grind)
    | exact resolve eq17615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17615
  have eq17630 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17623 eq274
    | exact resolve eq274 eq17623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq17623
  have eq17664 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17630
    | exact resolve eq17630 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17630
  have eq17666 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq723 y
       grind)
    | (have r₁ := eq17664
       have r₂ := eq723 y
       grind)
    | exact resolve eq17664 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq17664
  have eq17669 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17666 eq253
    | exact resolve eq253 eq17666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17687 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17666 eq183
    | exact resolve eq183 eq17666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17666
  have eq17705 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq17687
    | exact resolve eq17687 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17687
  have eq17706 : y = (k y x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17669
    | exact resolve eq17669 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17669
  have eq17707 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq703 eq17706
    | exact resolve eq17706 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq17706
  have eq17713 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq17705
       grind)
    | exact superpose eq17705 eq179
    | exact resolve eq179 eq17705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq17705
  have eq17757 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq185 y y X0
       have i₂ := eq17707
       grind)
    | exact superpose eq17707 eq185
    | exact resolve eq185 eq17707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq17707
  have eq17777 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17757 X0
       have i₂ := eq178 y X0
       grind)
    | exact superpose eq178 eq17757
    | exact resolve eq17757 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17757
  have eq17787 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq746 y
       have i₂ := eq17713
       grind)
    | exact superpose eq17713 eq746
    | (have j0 := eq746 y
       grind)
    | exact resolve eq746 eq17713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746 eq17713
  have eq17798 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq17787
  have eq17799 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq17798
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17798
    | exact resolve eq17798 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17798
  have eq18273 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq183 x x
       have i₂ := eq17777 X0
       grind)
    | exact superpose eq17777 eq183
    | (have j1 := eq17777 X0
       grind)
    | exact resolve eq183 eq17777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq17777
  have eq18295 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq18273 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18273
    | (have j0 := eq18273 X0
       grind)
    | exact resolve eq18273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18273
  have eq18296 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18295
  have eq18311 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq178 y X0
       have i₂ := eq18296 X0
       grind)
    | exact superpose eq18296 eq178
    | exact resolve eq178 eq18296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18296
  have eq18411 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18311 x
       grind)
    | exact superpose eq18311 eq18
    | (have j1 := eq18311 x
       grind)
    | exact resolve eq18 eq18311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18311
  have eq18445 : y = (M.op x y) := by grind
  clear eq18411
  have eq18456 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18445
       grind)
    | exact superpose eq18445 eq24
    | exact resolve eq24 eq18445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq18459 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq205
       have i₂ := eq18445
       grind)
    | exact superpose eq18445 eq205
    | exact resolve eq205 eq18445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq18509 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18456 eq20
    | exact resolve eq20 eq18456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21013 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17799 eq182
    | exact resolve eq182 eq17799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq17799
  have eq21038 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq21013 x
       have i₂ := eq178 sF3 x
       grind)
    | exact superpose eq178 eq21013
    | exact resolve eq21013 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq21013
  have eq21051 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq21038 X0
       have i₂ := eq18445
       grind)
    | exact superpose eq18445 eq21038
    | (have j0 := eq21038 X0
       grind)
    | exact resolve eq21038 eq18445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18445 eq21038
  have eq21472 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21051 eq26
    | (have j1 := eq21051 (σ x)
       grind)
    | exact resolve eq26 eq21051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21051
  have eq21491 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21472
  have eq21517 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq21491
       grind)
    | exact superpose eq21491 eq11
    | exact resolve eq11 eq21491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21491
  have eq21538 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq21517
  have eq21653 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq21538
       grind)
    | exact superpose eq21538 eq39
    | exact resolve eq39 eq21538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq21663 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21653
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21653
    | exact resolve eq21653 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21653
  have eq21668 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq21663
    | exact resolve eq21663 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21663
  have eq21673 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18509 eq21668
    | exact resolve eq21668 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21668
  have eq21684 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21673 eq6759
    | (have j0 := eq6759 (σ x)
       grind)
    | exact resolve eq6759 eq21673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6759 eq21673
  have eq21691 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21684
    | exact resolve eq21684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21684
  have eq21692 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21691
  have eq21709 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21692 eq253
    | exact resolve eq253 eq21692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253 eq21692
  have eq21758 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq21709
    | exact resolve eq21709 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21709
  have eq21764 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21538 eq21758
    | exact resolve eq21758 eq21538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21538 eq21758
  have eq21765 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21764
  have eq21967 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21765 eq27
    | exact resolve eq27 eq21765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21765
  have eq22005 : x = (M.op x y) := by
    first
    | (have r₁ := eq21967
       have r₂ := eq18509
       grind)
    | exact resolve eq21967 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21967
  have eq22007 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq22005
       grind)
    | exact superpose eq22005 eq22
    | exact resolve eq22 eq22005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq22012 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq186
       have i₂ := eq22005
       grind)
    | exact superpose eq22005 eq186
    | exact resolve eq186 eq22005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq22005
  have eq22123 : (σ x) = (σ y) := by
    first
    | exact superpose eq22007 eq18456
    | exact resolve eq18456 eq22007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18456
  have eq22124 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22007 eq20
    | exact resolve eq20 eq22007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22007
  have eq22414 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22123 eq26
    | exact resolve eq26 eq22123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq22913 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq22012 eq18459
    | exact resolve eq18459 eq22012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18459 eq22012
  have eq22952 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq22123 eq22913
    | exact resolve eq22913 eq22123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22913
  have eq22961 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq22952
    | exact resolve eq22952 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq22952
  have eq22968 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq18509 eq22961
    | exact resolve eq22961 eq18509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18509 eq22961
  have eq22972 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq22123 eq22968
    | exact resolve eq22968 eq22123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22123 eq22968
  have eq23328 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22414 eq11
    | exact resolve eq11 eq22414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22414
  have eq23349 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23328
  have eq23357 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22972 eq23349
    | exact resolve eq23349 eq22972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22972 eq23349
  have eq23358 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23357
  have eq23374 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23358 eq27
    | exact resolve eq27 eq23358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23358
  have eq23440 : False := by grind
  exact eq23440

/-- `Equation3180`: `x = (((y ◇ z) ◇ x) ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxx_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3180 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3180.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op (M.op X1 X2) X0) X1) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
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
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq77 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq66 (σ X0) (σ X0)
       grind)
    | exact superpose eq66 eq76
    | exact resolve eq76 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq90 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq64
    | exact resolve eq64 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq779 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq591 x y
       grind)
    | exact superpose eq591 eq16
    | (have j1 := eq591 x y
       grind)
    | exact resolve eq16 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 x
       have i₂ := eq591 x x
       grind)
    | exact superpose eq591 eq77
    | (have j1 := eq591 X0 X0
       grind)
    | exact resolve eq77 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq804 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq591 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq807 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq802 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq809 : ∀ X0 : G, (τ (σ (k X0 X0))) = (k (τ (σ (k X0 X0))) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq780 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq810 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq807 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq807
    | (have j0 := eq807 X0
       grind)
    | exact resolve eq807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq813 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq809 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 X0
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq820 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq805 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq805
    | (have j0 := eq805 (τ X0)
       grind)
    | exact resolve eq805 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq822 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq820 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq820
    | (have j0 := eq820 X0
       grind)
    | exact resolve eq820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq825 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq822 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq822
    | (have j0 := eq822 X0
       grind)
    | exact resolve eq822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq874 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq813 (τ X0)
       grind)
    | exact superpose eq813 eq19
    | (have j1 := eq813 (τ X0)
       grind)
    | exact resolve eq19 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq880 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq874 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq874
    | (have j0 := eq874 X0
       grind)
    | exact resolve eq874 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874
  have eq896 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq880 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq880
    | (have j0 := eq880 X0
       grind)
    | exact resolve eq880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq909 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq896 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq896
    | (have j0 := eq896 X0
       grind)
    | exact resolve eq896 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq936 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq909 (τ X0)
       grind)
    | exact superpose eq909 eq19
    | (have j1 := eq909 (τ X0)
       grind)
    | exact resolve eq19 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k (k (σ (τ X0)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq936 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq936
    | (have j0 := eq936 X0
       grind)
    | exact resolve eq936 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq958 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq942 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq942
    | (have j0 := eq942 X0
       grind)
    | exact resolve eq942 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq1045 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq958 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq958
    | (have j0 := eq958 (σ X0)
       grind)
    | exact resolve eq958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1079 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1045 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq1045
    | (have j0 := eq1045 X0
       grind)
    | exact resolve eq1045 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1094 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1079 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1079
    | (have j0 := eq1079 X0
       grind)
    | exact resolve eq1079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079
  have eq8497 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq810 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq810
    | exact resolve eq810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8519 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) X0) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq810 X0
       grind)
    | exact superpose eq810 eq77
    | (have j1 := eq810 X0
       grind)
    | exact resolve eq77 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq810
  have eq8579 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8519 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8519
    | (have j0 := eq8519 X0
       grind)
    | exact resolve eq8519 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8519
  have eq8582 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8497 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8497
    | (have j0 := eq8497 X0
       grind)
    | exact resolve eq8497 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8497
  have eq8586 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (σ (k (k (τ X0) (τ X0)) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8582 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8582
    | (have j0 := eq8582 X0
       grind)
    | exact resolve eq8582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8582
  have eq8588 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8586 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq8586
    | (have j0 := eq8586 X0
       grind)
    | exact resolve eq8586 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8586
  have eq8589 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8588 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq8588
    | (have j0 := eq8588 X0
       grind)
    | exact resolve eq8588 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq8588
  have eq8590 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8589 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8589
    | (have j0 := eq8589 X0
       grind)
    | exact resolve eq8589 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8589
  have eq8612 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq909 X0
       have i₂ := eq8590 X0
       grind)
    | exact superpose eq8590 eq909
    | (have j0 := eq909 X0
       have j1 := eq8590 X0
       grind)
    | exact resolve eq909 eq8590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909 eq8590
  have eq8667 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8612
  have eq8763 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X1) (k X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 (k X0 X0) X1
       have i₂ := eq8667 X0
       grind)
    | exact superpose eq8667 eq68
    | (have j1 := eq8667 X0
       grind)
    | exact resolve eq68 eq8667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8667
  have eq9055 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X1 (M.op (M.op X0 X1) X0)) ∨ (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X0 X0 X0
       have i₂ := eq8763 X0 X1
       grind)
    | exact superpose eq8763 eq90
    | (have j1 := eq8763 X0 X2
       grind)
    | exact resolve eq90 eq8763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8763
  have eq9124 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X0)) X2) = X2 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9055 X0 X1 X2
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq9055
    | (have j0 := eq9055 X0 X1 X2
       grind)
    | exact resolve eq9055 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9055
  have eq9552 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9124 X0 (M.op (M.op X0 X0) (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9124
  have eq9553 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (k X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq9552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9552
  have eq9588 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 X0
       have i₂ := eq9553 X0
       grind)
    | exact superpose eq9553 eq9
    | exact resolve eq9 eq9553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9590 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 (k X0 X0) X0 X0
       have i₂ := eq9553 X0
       grind)
    | exact superpose eq9553 eq65
    | exact resolve eq65 eq9553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9553
  have eq9651 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9590 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq9590
    | exact resolve eq9590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9652 : ∀ X0 : G, (τ X0) = (M.op (τ (k X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9590 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9590
    | exact resolve eq9590 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq9590
  have eq9697 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9588 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq9588
    | exact resolve eq9588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9588
  have eq10230 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9697 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq9697
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq9697 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9697
  have eq10293 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10230
  have eq17409 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
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
  have eq17519 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17409 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq17409
    | (have j0 := eq17409 X0 X1
       grind)
    | exact resolve eq17409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17409
  have eq24875 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8579 X0
       have i₂ := eq17519 X0 X0
       grind)
    | exact superpose eq17519 eq8579
    | (have j0 := eq8579 X0
       have j1 := eq17519 X0 X0
       grind)
    | exact resolve eq8579 eq17519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8579
  have eq24962 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24875 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24875
  have eq24990 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq24962 X0
       have j1 := eq825 X0
       grind)
    | (have r₁ := eq24962 X0
       have r₂ := eq825 X0
       grind)
    | exact resolve eq24962 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq24962
  have eq25499 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10293 X0
       have i₂ := eq24990 X0
       grind)
    | exact superpose eq24990 eq10293
    | (have j0 := eq10293 X0
       have j1 := eq24990 X0
       grind)
    | exact resolve eq10293 eq24990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10293 eq24990
  have eq25571 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k (k X0 X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25499 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25499
  have eq25679 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1094 X0
       have i₂ := eq25571 X0
       grind)
    | exact superpose eq25571 eq1094
    | (have j0 := eq1094 X0
       have j1 := eq25571 X0
       grind)
    | exact resolve eq1094 eq25571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq25571
  have eq25752 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25679 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25679
  have eq25873 : ∀ X0 : G, (τ (σ (M.op X0 X0))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq25752 X0
       grind)
    | exact superpose eq25752 eq10
    | (have j1 := eq25752 X0
       grind)
    | exact resolve eq10 eq25752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25752
  have eq25940 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq25873 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq25873
    | (have j0 := eq25873 X0
       grind)
    | exact resolve eq25873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25873
  have eq25995 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq25940
  have eq26126 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25995 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25995
  have eq26228 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9651 X0
       have i₂ := eq26126 X0
       grind)
    | exact superpose eq26126 eq9651
    | exact resolve eq9651 eq26126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9651
  have eq26229 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq9652 X0
       have i₂ := eq26126 X0
       grind)
    | exact superpose eq26126 eq9652
    | exact resolve eq9652 eq26126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9652
  have eq26303 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26126 (σ X0)
       grind)
    | exact superpose eq26126 eq15
    | exact resolve eq15 eq26126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26362 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq26303 X0
       have i₂ := eq26126 X0
       grind)
    | exact superpose eq26126 eq26303
    | exact resolve eq26303 eq26126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26126 eq26303
  have eq26628 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (M.op X1 (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq26228 X0
       grind)
    | exact superpose eq26228 eq90
    | exact resolve eq90 eq26228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26801 : ∀ X0 X1 : G, (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) = (M.op X1 (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq26229 X0
       grind)
    | exact superpose eq26229 eq90
    | exact resolve eq90 eq26229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26229
  have eq51510 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq779
       have i₂ := eq17519 x y
       grind)
    | exact superpose eq17519 eq779
    | (have j1 := eq17519 (σ x) (σ y)
       grind)
    | (have r₁ := eq779
       have r₂ := eq17519 x y
       grind)
    | exact resolve eq779 eq17519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779 eq17519
  have eq51511 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq51510
  have eq51513 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq51511
       have i₂ := eq26362 x
       grind)
    | exact superpose eq26362 eq51511
    | exact resolve eq51511 eq26362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26362 eq51511
  have eq1213190 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq66 y x
       have i₂ := eq51513
       grind)
    | exact superpose eq51513 eq66
    | exact resolve eq66 eq51513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51513
  have eq1251442 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq68 (σ y) (σ x) X0
       have i₂ := eq1213190
       grind)
    | exact superpose eq1213190 eq68
    | exact resolve eq68 eq1213190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1213190
  have eq1252091 : ∀ X0 : G, (σ y) = (σ (M.op x x)) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1251442 X0
       have i₂ := eq64 (σ y) X0
       grind)
    | exact superpose eq64 eq1251442
    | exact resolve eq1251442 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251442
  have eq1252518 : ∀ X0 : G, (M.op x x) = (τ (σ y)) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1252091 X0
       grind)
    | exact superpose eq1252091 eq10
    | (have j1 := eq1252091 X0
       grind)
    | exact resolve eq10 eq1252091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252091
  have eq1253079 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op y y) ∨ (M.op (σ y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1252518 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1252518
    | (have j0 := eq1252518 X0
       grind)
    | exact resolve eq1252518 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1252518
  have eq1253080 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op x x) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1253079 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253079
  have eq1253443 : ∀ X0 X1 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op (M.op y X0) y)) ∨ y = (M.op x x) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 y y
       have i₂ := eq1253080 X0
       grind)
    | exact superpose eq1253080 eq90
    | (have j1 := eq1253080 X1
       grind)
    | exact resolve eq90 eq1253080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq1253080
  have eq1253824 : ∀ X0 X1 : G, y = (M.op x x) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1253443 X1 X1
       have i₂ := eq64 y X1
       grind)
    | exact superpose eq64 eq1253443
    | (have j0 := eq1253443 X0 X1
       grind)
    | exact resolve eq1253443 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253443
  have eq1254145 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26228 x
       have i₂ := eq1253824 X0 X1
       grind)
    | exact superpose eq1253824 eq26228
    | (have j1 := eq1253824 X0 (σ x)
       grind)
    | exact resolve eq26228 eq1253824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26228
  have eq1254431 : ∀ X0 X1 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ (M.op (σ y) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq66 x x
       have i₂ := eq1253824 X0 X1
       grind)
    | exact superpose eq1253824 eq66
    | (have j1 := eq1253824 x X1
       grind)
    | exact resolve eq66 eq1253824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1253824
  have eq1256564 : ∀ X0 : G, y ≠ y ∨ y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1254431 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254431
  have eq1256565 : ∀ X0 : G, y = (M.op x y) ∨ (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1256564 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256564
  have eq1257428 : ∀ X0 X1 X2 : G, (M.op (σ y) X2) = X2 ∨ (M.op (M.op (M.op X0 X1) (M.op (M.op y X0) x)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 x y X1
       have i₂ := eq1256565 X2
       grind)
    | exact superpose eq1256565 eq62
    | (have j1 := eq1256565 X2
       grind)
    | exact resolve eq62 eq1256565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq1256565
  have eq1267019 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (σ y)) X0) (τ (σ y))) = (M.op X0 (M.op (M.op (τ (σ y)) X0) (τ (σ y)))) ∨ (M.op (M.op (M.op X1 X2) (M.op (M.op y X1) x)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26801 (σ y) X1
       have i₂ := eq1257428 X0 X1 (σ y)
       grind)
    | exact superpose eq1257428 eq26801
    | (have j1 := eq1257428 X1 X2 X2
       grind)
    | exact resolve eq26801 eq1257428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26801 eq1257428
  have eq1267719 : ∀ X0 X1 X2 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (M.op (M.op (M.op X1 X2) (M.op (M.op y X1) x)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1267019 X1 X1 X2
       have i₂ := eq64 (τ (σ y)) X1
       grind)
    | exact superpose eq64 eq1267019
    | (have j0 := eq1267019 X0 X1 X2
       grind)
    | exact resolve eq1267019 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267019
  have eq1267847 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op y X1) x)) X2) = X2 ∨ y = (M.op X0 y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1267719 X0 X1 X2
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1267719
    | (have j0 := eq1267719 X0 X1 X2
       grind)
    | exact resolve eq1267719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267719
  have eq1269973 : ∀ X0 : G, y ≠ y ∨ y = (M.op (M.op (M.op X0 y) (M.op (M.op y X0) x)) y) := by
    intro X0
    first
    | (have j0 := eq1267847 (M.op (M.op X0 y) (M.op (M.op y X0) x)) X0 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267847
  have eq1269974 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (M.op (M.op y X0) x)) y) := by
    intro X0
    first
    | (have j0 := eq1269973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269973
  have eq1270717 : y = (M.op (M.op (M.op y y) x) y) := by
    first
    | (have i₁ := eq65 (M.op (M.op y y) x) y y
       have i₂ := eq1269974 y
       grind)
    | exact superpose eq1269974 eq65
    | exact resolve eq65 eq1269974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269974
  have eq1271249 : y = (M.op x y) := by
    first
    | (have i₁ := eq65 x y y
       have i₂ := eq1270717
       grind)
    | exact superpose eq1270717 eq65
    | exact resolve eq65 eq1270717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1270717
  have eq1320695 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ y = (M.op X0 y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1254145 X0 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254145
  have eq1320696 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1320695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320695
  have eq1320802 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq64 (σ y) (σ x)
       have i₂ := eq1320696 X0
       grind)
    | exact superpose eq1320696 eq64
    | (have j1 := eq1320696 X0
       grind)
    | exact resolve eq64 eq1320696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320696
  have eq1321180 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1320802 X0
       grind)
    | exact superpose eq1320802 eq16
    | (have j1 := eq1320802 X0
       grind)
    | exact resolve eq16 eq1320802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320802
  have eq1321602 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1321180 X0
       have i₂ := eq1271249
       grind)
    | exact superpose eq1271249 eq1321180
    | (have j0 := eq1321180 X0
       grind)
    | exact resolve eq1321180 eq1271249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271249 eq1321180
  have eq1321603 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1321602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321602
  have eq1321674 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq26628 y x
       have i₂ := eq1321603 y
       grind)
    | exact superpose eq1321603 eq26628
    | exact resolve eq26628 eq1321603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26628
  have eq1323597 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1321674 x
       have i₂ := eq64 (σ y) x
       grind)
    | exact superpose eq64 eq1321674
    | exact resolve eq1321674 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1321674
  have eq1330405 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1323597 (σ x)
       grind)
    | exact superpose eq1323597 eq16
    | exact resolve eq16 eq1323597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323597
  have eq1330801 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1330405
       have i₂ := eq1321603 x
       grind)
    | exact superpose eq1321603 eq1330405
    | exact resolve eq1330405 eq1321603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321603 eq1330405
  have eq1330802 : False := by grind
  exact eq1330802
