import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq83 X0 X0
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq200 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq196 X1 X0
       grind)
    | (have r₁ := eq202 X1 X0
       have r₂ := eq196 X0 X1
       grind)
    | (have r₁ := eq202 X1 (k X0 X1)
       have r₂ := eq196 X0 X1
       grind)
    | (have r₁ := eq202 X1 X1
       have r₂ := eq196 X1 X1
       grind)
    | exact resolve eq202 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq202
  have eq523 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq205
    | exact resolve eq205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 y x
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 y x
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq546 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq523
    | (have j0 := eq523 X0 X1
       grind)
    | exact resolve eq523 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq523
  have eq548 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq607 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq548 (τ X0) X1
       grind)
    | exact superpose eq548 eq18
    | (have j1 := eq548 (τ X0) X1
       grind)
    | exact resolve eq18 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq548
  have eq845 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq607 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq607
    | exact resolve eq607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq898 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq845
    | (have j0 := eq845 X0 X1
       grind)
    | exact resolve eq845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq531
       have i₂ := eq898 x y
       grind)
    | exact superpose eq898 eq531
    | (have j1 := eq898 (σ x) (σ y)
       grind)
    | (have r₁ := eq531
       have r₂ := eq898 x y
       grind)
    | exact resolve eq531 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq999 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq998
  have eq1005 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq999
  have eq1043 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq531
       have i₂ := eq1005
       grind)
    | exact superpose eq1005 eq531
    | exact resolve eq531 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq1005
  have eq1044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1043
  have eq1045 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1044
  have eq1060 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1045
  have eq1067 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1060
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1060
    | exact resolve eq1060 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1105 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq16
    | exact resolve eq16 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1067
  have eq1113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1105
       have i₂ := eq898 x y
       grind)
    | exact superpose eq898 eq1105
    | (have j1 := eq898 x y
       grind)
    | (have r₁ := eq1105
       have r₂ := eq898 x y
       grind)
    | exact resolve eq1105 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq1114 : x = (M.op y y) := by grind
  clear eq1113
  have eq1150 : (M.op x y) = (k x y) := by grind
  clear eq1114
  have eq1156 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1105
       have i₂ := eq1150
       grind)
    | exact superpose eq1150 eq1105
    | exact resolve eq1105 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq1150
  have eq1159 : False := by grind
  exact eq1159

/-- `Equation2663`: `x = ((x ◇ y) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pxy_pyx_x_pxy_Equation2663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
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
  have eq50 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq59 (σ X0)
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq43
    | exact resolve eq43 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq63 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq62
       have i₂ := eq59 sF2
       grind)
    | exact superpose eq59 eq62
    | exact resolve eq62 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq61
    | exact resolve eq61 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq59 sF2
       grind)
    | exact superpose eq59 eq49
    | exact resolve eq49 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq59 x
       grind)
    | exact superpose eq59 eq70
    | exact resolve eq70 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq73 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | exact superpose eq20 eq90
    | exact resolve eq90 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq93 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq101 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq105 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq101
       have i₂ := eq59 sF3
       grind)
    | exact superpose eq59 eq101
    | exact resolve eq101 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq107 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq59 y
       grind)
    | exact superpose eq59 eq105
    | exact resolve eq105 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq119 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq116
       have i₂ := eq59 sF1
       grind)
    | exact superpose eq59 eq116
    | exact resolve eq116 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq119
    | exact resolve eq119 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq176 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq242 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq59 (τ X0)
       grind)
    | exact superpose eq59 eq34
    | exact resolve eq34 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq253 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq242 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq242
    | exact resolve eq242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq254 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq253 X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq253
    | exact resolve eq253 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq253
  have eq318 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) y) := by
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq322 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq325
    | exact resolve eq325 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq331 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq322
       have i₂ := eq52 sF4 sF4
       grind)
    | exact superpose eq52 eq322
    | exact resolve eq322 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq333 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) y) := by
    first
    | (have i₁ := eq320
       have i₂ := eq52 sF0 sF0
       grind)
    | exact superpose eq52 eq320
    | exact resolve eq320 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq335 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq318 X0 X1
       have i₂ := eq52 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq318
    | exact resolve eq318 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq336 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq329
    | exact resolve eq329 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq340 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq335
    | exact resolve eq335 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq344 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq324 (M.op X0 X1) X2
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq324
    | exact resolve eq324 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq324 X0 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq324
    | exact resolve eq324 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : (σ (M.op (k x y) (k x y))) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq64 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq64
    | exact resolve eq64 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq14
    | exact resolve eq14 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq324 (σ X0) X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq324
    | exact resolve eq324 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq404 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq64 (M.op X0 X0)
       grind)
    | exact superpose eq64 eq398
    | exact resolve eq398 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq411 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq404 X0
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq404
    | exact resolve eq404 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq458 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq459 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq458 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq458
    | (have j0 := eq458 X0 X1
       grind)
    | exact resolve eq458 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq460 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X1
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq459
    | (have j0 := eq459 X0 X1
       grind)
    | exact resolve eq459 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq538 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq460 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq460
    | (have j0 := eq460 x X0
       grind)
    | exact resolve eq460 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq576 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op x x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq538 X0
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq538
    | (have j0 := eq538 X0
       grind)
    | exact resolve eq538 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq589 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (σ X0)) ∨ (M.op (σ x) (σ x)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq576 X0
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq576
    | (have j0 := eq576 X0
       grind)
    | exact resolve eq576 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq625 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq16
    | exact resolve eq16 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq743 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) (σ y)) := by
    first
    | exact superpose eq331 eq52
    | exact resolve eq52 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq746 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq743
       have i₂ := eq52 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq52 eq743
    | exact resolve eq743 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq747 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq746
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq746
    | exact resolve eq746 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq748 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq747
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq747
    | exact resolve eq747 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq798 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) (M.op (M.op (M.op x y) (M.op x y)) (M.op x y))) y) := by
    first
    | exact superpose eq333 eq52
    | exact resolve eq52 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq801 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op x y)) y) := by
    first
    | (have i₁ := eq798
       have i₂ := eq52 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq52 eq798
    | exact resolve eq798 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq802 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq801
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq801
    | exact resolve eq801 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq803 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq802
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq802
    | exact resolve eq802 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq813 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq71 eq625
    | exact resolve eq625 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq841 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq813
       have i₂ := eq52 sF2 sF2
       grind)
    | exact superpose eq52 eq813
    | exact resolve eq813 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq846 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq748 eq841
    | exact resolve eq841 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq841
  have eq847 : (M.op (M.op x x) x) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq846
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq846
    | exact resolve eq846 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq848 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq847
       have i₂ := eq803
       grind)
    | exact superpose eq803 eq847
    | exact resolve eq847 eq803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803 eq847
  have eq898 : (σ (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq848 eq15
    | exact resolve eq15 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1004 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq748 eq346
    | exact resolve eq346 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq748
  have eq2934 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op (M.op X0 X1) (M.op X0 X1))) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq336 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2955 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq336 (σ X0) (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq336
    | exact resolve eq336 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq2974 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2955 X0
       have i₂ := eq400 X0 (σ X0)
       grind)
    | exact superpose eq400 eq2955
    | exact resolve eq2955 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq2955
  have eq2994 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2934 X0 X1
       have i₂ := eq324 (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq324 eq2934
    | exact resolve eq2934 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2934
  have eq3170 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X0 X0) X1) (M.op X0 X1)) X1
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq52
    | exact resolve eq52 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq3173 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3170 X0 X1
       have i₂ := eq52 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       grind)
    | exact superpose eq52 eq3170
    | exact resolve eq3170 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3170
  have eq3218 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3173 X0 X1
       have i₂ := eq52 (M.op X0 X0) X1
       grind)
    | exact superpose eq52 eq3173
    | exact resolve eq3173 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3173
  have eq3254 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3218 X1 X1
       have i₂ := eq52 X1 X1
       grind)
    | exact superpose eq52 eq3218
    | exact resolve eq3218 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3218
  have eq3277 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3254 X0 X1
       have i₂ := eq336 X0 X1
       grind)
    | exact superpose eq336 eq3254
    | exact resolve eq3254 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq3254
  have eq4719 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq589 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq589
    | (have j0 := eq589 y
       grind)
    | exact resolve eq589 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq4743 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4719
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4719
    | exact resolve eq4719 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4761 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq4743
    | exact resolve eq4743 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743
  have eq4769 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq4761
    | exact resolve eq4761 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4761
  have eq4774 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4769
       have i₂ := eq107
       grind)
    | exact superpose eq107 eq4769
    | exact resolve eq4769 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4769
  have eq8153 : (σ y) = (M.op (σ (M.op (M.op y y) y)) (σ y)) := by
    first
    | (have i₁ := eq411 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq411
    | (have j0 := eq411 y
       grind)
    | exact resolve eq411 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq411
  have eq8466 : ∀ X0 : G, (σ y) = (M.op (σ (M.op (M.op y X0) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8153
       have i₂ := eq3277 y X0
       grind)
    | (have i₁ := eq8153
       have i₂ := eq3277 y y
       grind)
    | exact superpose eq3277 eq8153
    | exact resolve eq8153 eq3277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153
  have eq15327 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq344 X0 X0 X2
       have i₂ := eq3277 X0 X1
       grind)
    | (have i₁ := eq344 X1 X1 X2
       have i₂ := eq3277 X1 X1
       grind)
    | exact superpose eq3277 eq344
    | exact resolve eq344 eq3277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3277
  have eq31687 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x x) y) X0) X0) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15327 y y x
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq15327
    | exact resolve eq15327 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq31688 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31687 x
       have i₂ := eq344 x y x
       grind)
    | exact superpose eq344 eq31687
    | exact resolve eq31687 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31687
  have eq31735 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31688
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31688
    | exact resolve eq31688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31688
  have eq31736 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31735
  have eq31777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31736 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq31736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31777
    | exact resolve eq31777 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31777
  have eq31789 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq31778
       have r₂ := eq27
       grind)
    | exact resolve eq31778 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31778
  have eq31793 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31789
    | exact resolve eq31789 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31789
  have eq31859 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31793 eq15327
    | exact resolve eq15327 eq31793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31793
  have eq31860 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq31859 x
       have i₂ := eq344 sF2 sF3 x
       grind)
    | exact superpose eq344 eq31859
    | exact resolve eq31859 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31859
  have eq31908 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq31860
    | exact resolve eq31860 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31860
  have eq31909 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31908
  have eq31933 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31909 eq73
    | (have r₁ := eq73
       have r₂ := eq31909
       grind)
    | exact resolve eq73 eq31909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq32001 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq31933
  have eq33918 : (σ y) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq4774 eq2994
    | exact resolve eq2994 eq4774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994 eq4774
  have eq33939 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33918
       have i₂ := eq324 sF2 sF3
       grind)
    | exact superpose eq324 eq33918
    | exact resolve eq33918 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33918
  have eq67691 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq32001 eq14
    | exact resolve eq14 eq32001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32001
  have eq67717 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq51 eq67691
    | exact resolve eq67691 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67691
  have eq67737 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq67717 eq58
    | exact resolve eq58 eq67717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq67717
  have eq67758 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq67737
    | exact resolve eq67737 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67737
  have eq68371 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq67758
       grind)
    | exact superpose eq67758 eq72
    | (have r₁ := eq72
       have r₂ := eq67758
       grind)
    | exact resolve eq72 eq67758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq67758
  have eq68447 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq68371
  have eq68448 : (M.op x y) = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq68447
  have eq69222 : (σ y) = (M.op (σ (M.op (M.op x y) y)) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8466 y
       have i₂ := eq68448
       grind)
    | exact superpose eq68448 eq8466
    | exact resolve eq8466 eq68448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8466 eq68448
  have eq69295 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq898 eq69222
    | exact resolve eq69222 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69222
  have eq132222 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ y) (σ y)) X0) X0) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq69295 eq15327
    | exact resolve eq15327 eq69295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15327 eq69295
  have eq132227 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132222 x
       have i₂ := eq324 sF3 x
       grind)
    | exact superpose eq324 eq132222
    | exact resolve eq132222 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132222
  have eq132248 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132227
       have i₂ := eq52 sF4 sF3
       grind)
    | exact superpose eq52 eq132227
    | exact resolve eq132227 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq132227
  have eq132259 : (σ x) = (σ y) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51 eq132248
    | exact resolve eq132248 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq132248
  have eq132260 : x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq132259
  have eq132269 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq132260
       grind)
    | exact superpose eq132260 eq44
    | exact resolve eq44 eq132260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq132276 : (σ (M.op x x)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq388
       have i₂ := eq132260
       grind)
    | exact superpose eq132260 eq388
    | exact resolve eq388 eq132260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq132260
  have eq132297 : (M.op (σ x) (σ x)) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132276
       have i₂ := eq63
       grind)
    | exact superpose eq63 eq132276
    | exact resolve eq132276 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132276
  have eq132304 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq132269
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq132269
    | exact resolve eq132269 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132269
  have eq136327 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq31736 eq132297
    | exact resolve eq132297 eq31736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136343 : ∀ X0 X1 : G, (M.op (k (σ x) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ x) (σ x)) X0) X1) X1) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq132297 eq344
    | exact resolve eq344 eq132297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132297
  have eq136421 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (k (σ x) (σ y)) X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq136343 x x
       have i₂ := eq344 sF2 x x
       grind)
    | exact superpose eq344 eq136343
    | exact resolve eq136343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136343
  have eq139183 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq31736 eq136421
    | exact resolve eq136421 eq31736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31736 eq136421
  have eq263019 : (M.op x x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq136327 eq71
    | exact resolve eq71 eq136327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq263038 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq136327 eq31909
    | exact resolve eq31909 eq136327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31909 eq136327
  have eq263222 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq263038
  have eq263269 : (M.op (M.op x y) (M.op x y)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq176 eq263019
    | exact resolve eq263019 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq263019
  have eq264035 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq263222 eq324
    | exact resolve eq324 eq263222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq263222
  have eq308209 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq139183
    | (have j0 := eq139183 (σ y)
       grind)
    | exact resolve eq139183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139183
  have eq311822 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op (M.op (M.op x x) X0) X1) X1) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq263269 eq344
    | exact resolve eq344 eq263269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263269
  have eq311973 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq311822 X0 x
       have i₂ := eq344 x X0 x
       grind)
    | exact superpose eq344 eq311822
    | exact resolve eq311822 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq311822
  have eq363542 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq311973 eq898
    | exact resolve eq898 eq311973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq311973
  have eq364080 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq363542
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq363542
    | exact resolve eq363542 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363542
  have eq364115 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq364080
    | exact resolve eq364080 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364080
  have eq365926 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq364115 eq264035
    | exact resolve eq264035 eq364115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264035 eq364115
  have eq365951 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq365926
  have eq374733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq365951 eq308209
    | exact resolve eq308209 eq365951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308209 eq365951
  have eq374783 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq374733
  have eq374786 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq374783
       have r₂ := eq27
       grind)
    | exact resolve eq374783 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374783
  have eq374790 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63
       have i₂ := eq374786
       grind)
    | exact superpose eq374786 eq63
    | exact resolve eq63 eq374786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq374850 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2974 x
       have i₂ := eq374786
       grind)
    | exact superpose eq374786 eq2974
    | exact resolve eq2974 eq374786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974 eq374786
  have eq374964 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq374850
    | exact resolve eq374850 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374850
  have eq374985 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq374790
    | exact resolve eq374790 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374790
  have eq374999 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq374964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq374964
    | exact resolve eq374964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq374964
  have eq376586 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq374985 eq1004
    | exact resolve eq1004 eq374985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1789728 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33939 eq132304
    | exact resolve eq132304 eq33939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33939 eq132304
  have eq1789999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1789728
  have eq1790152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1789999 eq374985
    | exact resolve eq374985 eq1789999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374985 eq1789999
  have eq1790451 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1790152
  have eq1790540 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1790451
       have r₂ := eq27
       grind)
    | exact resolve eq1790451 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790451
  have eq1790562 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1790540 eq27
    | exact resolve eq27 eq1790540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1790826 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1790540 eq376586
    | exact resolve eq376586 eq1790540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376586
  have eq1791025 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq1790826
  have eq1791157 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq1791025
    | exact resolve eq1791025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791025
  have eq1792522 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1790540 eq1791157
    | exact resolve eq1791157 eq1790540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790540 eq1791157
  have eq1792570 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq1792522
  have eq1795687 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1792570 eq374999
    | exact resolve eq374999 eq1792570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374999 eq1792570
  have eq1795896 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq1795687
  have eq1795997 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1795896
       have r₂ := eq1790562
       grind)
    | exact resolve eq1795896 eq1790562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790562 eq1795896
  have eq1796043 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1795997 eq26
    | exact resolve eq26 eq1795997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1796044 : y = (τ (σ x)) := by
    first
    | exact superpose eq1795997 eq29
    | exact resolve eq29 eq1795997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1795997
  have eq1796349 : x = y := by
    first
    | exact superpose eq28 eq1796044
    | exact resolve eq1796044 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1796044
  have eq1796423 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1796349
       grind)
    | exact superpose eq1796349 eq18
    | exact resolve eq18 eq1796349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1796349
  have eq1797800 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq63
       have i₂ := eq1796423
       grind)
    | exact superpose eq1796423 eq63
    | exact resolve eq63 eq1796423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1796423
  have eq1798152 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1796043 eq1797800
    | exact resolve eq1797800 eq1796043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796043 eq1797800
  have eq1798228 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1798152
    | exact resolve eq1798152 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1798152
  have eq1798279 : False := by grind
  exact eq1798279

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_y_pxx_x_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq100 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq100
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq109
    | exact resolve eq109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq524 : ∀ X0 : G, (k (τ X0) (k x x)) = (τ (k X0 (k (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq282 X0 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq282
    | exact resolve eq282 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq282
  have eq558 : ∀ X0 : G, (τ (k X0 (M.op (σ x) (σ x)))) = (k (τ X0) (k x x)) := by
    intro X0
    first
    | (have i₁ := eq524 X0
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq524
    | exact resolve eq524 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq561 : ∀ X0 : G, (k (τ X0) (M.op x x)) = (τ (k X0 (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq558
    | exact resolve eq558 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq637 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq638 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq646 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1110 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq658 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq658
    | (have j0 := eq658 x y X0
       grind)
    | exact resolve eq658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1111 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq658
    | (have j0 := eq658 (σ x) (σ y) X0
       grind)
    | exact resolve eq658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq658 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq658
    | (have j0 := eq658 x X0 y
       grind)
    | exact resolve eq658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq658
    | (have j0 := eq658 (σ x) X0 (σ y)
       grind)
    | exact resolve eq658 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq658 X0 X1 x
       grind)
    | exact superpose eq658 eq14
    | exact resolve eq14 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 X0 (M.op X0 X1)
       have i₂ := eq658 X0 X0 X1
       grind)
    | exact superpose eq658 eq1130
    | exact resolve eq1130 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1130 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq1130 X0 (M.op X0 X0)
       grind)
    | exact superpose eq1130 eq1130
    | exact resolve eq1130 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1206 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1130 (M.op X0 X1) X0
       grind)
    | exact superpose eq1130 eq55
    | exact resolve eq55 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1130 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1130 eq14
    | exact resolve eq14 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1206 X0 X1
       have i₂ := eq658 X0 X1 X1
       grind)
    | exact superpose eq658 eq1206
    | exact resolve eq1206 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1233 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1202 (σ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1202
    | exact resolve eq1202 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq1202
  have eq1313 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1125 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1125
    | (have j0 := eq1125 y
       grind)
    | exact resolve eq1125 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1351 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1313
       have i₂ := eq1110 X0
       grind)
    | exact superpose eq1110 eq1313
    | exact resolve eq1313 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1502 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1126
    | (have j0 := eq1126 (σ y)
       grind)
    | exact resolve eq1126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1540 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1111 eq1502
    | exact resolve eq1502 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1201 (M.op x x) y
       have i₂ := eq1313
       grind)
    | exact superpose eq1313 eq1201
    | exact resolve eq1201 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1810 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1201
    | exact resolve eq1201 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1812 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1502 eq1201
    | exact resolve eq1201 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1816 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq245 eq1201
    | exact resolve eq1201 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1816
       have i₂ := eq1130 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1130 eq1816
    | exact resolve eq1816 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1850 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1812
       have i₂ := eq1130 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1130 eq1812
    | exact resolve eq1812 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq1852 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1810
       have i₂ := eq1130 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1130 eq1810
    | exact resolve eq1810 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1856 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1806
       have i₂ := eq1130 x (M.op x x)
       grind)
    | exact superpose eq1130 eq1806
    | exact resolve eq1806 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq1806
  have eq1894 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1846 eq245
    | exact resolve eq245 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1902 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1846 eq658
    | exact resolve eq658 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1915 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1902 x
       have i₂ := eq658 sF4 sF2 x
       grind)
    | exact superpose eq658 eq1902
    | exact resolve eq1902 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1902
  have eq1919 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq1846 eq1915
    | exact resolve eq1915 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq1977 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1852 eq236
    | exact resolve eq236 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1986 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1852 eq658
    | exact resolve eq658 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2000 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq1986 x
       have i₂ := eq658 sF0 x x
       grind)
    | exact superpose eq658 eq1986
    | exact resolve eq1986 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986
  have eq2004 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq1852 eq2000
    | exact resolve eq2000 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2000
  have eq2176 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1846 eq1850
    | exact resolve eq1850 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq2177 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1852 eq1856
    | exact resolve eq1856 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq2906 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1227 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1227
    | exact resolve eq1227 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2908 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq236 eq1227
    | exact resolve eq1227 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2910 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq245 eq1227
    | exact resolve eq1227 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq2914 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1201 X0 X1
       grind)
    | exact superpose eq1201 eq1227
    | exact resolve eq1227 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2992 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2914 X0 X1
       have i₂ := eq1211 X0 X0
       grind)
    | exact superpose eq1211 eq2914
    | exact resolve eq2914 eq1211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211 eq2914
  have eq2998 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2992 X0 X1
       have i₂ := eq658 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq658 eq2992
    | exact resolve eq2992 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq2999 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2998 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2998
    | exact resolve eq2998 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2998
  have eq3463 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2908 eq2999
    | exact resolve eq2999 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999
  have eq3551 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3463
       have i₂ := eq658 sF0 y y
       grind)
    | exact superpose eq658 eq3463
    | exact resolve eq3463 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3463
  have eq3587 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq236 eq3551
    | exact resolve eq3551 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq3551
  have eq3948 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2906 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2906 X0 X1
       grind)
    | exact superpose eq2906 eq2906
    | exact resolve eq2906 eq2906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3963 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2908 eq2906
    | exact resolve eq2906 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3973 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2910 eq2906
    | exact resolve eq2906 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4031 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq3973
       have i₂ := eq1227 sF2 sF4
       grind)
    | exact superpose eq1227 eq3973
    | exact resolve eq3973 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3973
  have eq4039 : (M.op (M.op x y) y) = (M.op (M.op x x) (M.op x y)) := by
    first
    | (have i₁ := eq3963
       have i₂ := eq1227 x sF0
       grind)
    | exact superpose eq1227 eq3963
    | exact resolve eq3963 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq4050 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3948 X0 X1
       have i₂ := eq1227 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1227 eq3948
    | exact resolve eq3948 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948
  have eq4076 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1126 eq4031
    | exact resolve eq4031 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq4031
  have eq4080 : (M.op (M.op x y) y) = (M.op (M.op x x) x) := by
    first
    | exact superpose eq1125 eq4039
    | exact resolve eq4039 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq4039
  have eq4085 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4050 X0 X1
       have i₂ := eq658 X0 X0 X1
       grind)
    | exact superpose eq658 eq4050
    | exact resolve eq4050 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050
  have eq4597 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1351 eq240
    | (have j0 := eq240 y X1
       grind)
    | exact resolve eq240 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq4598 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq1852 eq4597
    | exact resolve eq4597 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4597
  have eq4615 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4598 eq2906
    | exact resolve eq2906 eq4598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4598
  have eq4621 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq1977 eq4615
    | exact resolve eq4615 eq1977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977 eq4615
  have eq4629 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2177 eq4621
    | exact resolve eq4621 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177 eq4621
  have eq5015 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1540 eq249
    | (have j0 := eq249 (σ y) X1
       grind)
    | exact resolve eq249 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq5016 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1846 eq5015
    | exact resolve eq5015 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5015
  have eq5333 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5016 eq2906
    | exact resolve eq2906 eq5016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5016
  have eq5341 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1894 eq5333
    | exact resolve eq5333 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894 eq5333
  have eq5349 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2176 eq5341
    | exact resolve eq5341 eq2176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176 eq5341
  have eq6309 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4085 X0 X2
       have i₂ := eq4085 X0 X1
       grind)
    | (have i₁ := eq4085 X1 X1
       have i₂ := eq4085 X1 X1
       grind)
    | exact superpose eq4085 eq4085
    | exact resolve eq4085 eq4085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6320 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4085 x X0
       have i₂ := eq4080
       grind)
    | exact superpose eq4080 eq4085
    | exact resolve eq4085 eq4080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4080
  have eq6321 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) X0) X0) := by
    intro X0
    first
    | exact superpose eq4076 eq4085
    | exact resolve eq4085 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq6373 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1201 X0 X2
       have i₂ := eq4085 X0 X1
       grind)
    | (have i₁ := eq1201 X1 X1
       have i₂ := eq4085 X1 X1
       grind)
    | exact superpose eq4085 eq1201
    | exact resolve eq1201 eq4085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11972 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1351 eq637
    | (have j0 := eq637 y X1 X2
       grind)
    | exact resolve eq637 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq1351
  have eq11973 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1852 eq11972
    | exact resolve eq11972 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852 eq11972
  have eq11974 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4629 eq11973
    | exact resolve eq11973 eq4629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4629 eq11973
  have eq12049 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq11974 y
       have i₂ := eq1110 X0
       grind)
    | exact superpose eq1110 eq11974
    | exact resolve eq11974 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq11974
  have eq12100 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq12049 x
       have i₂ := eq658 sF0 x (M.op x x)
       grind)
    | exact superpose eq658 eq12049
    | exact resolve eq12049 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12049
  have eq12122 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq12100
       have i₂ := eq1227 sF0 x
       grind)
    | exact superpose eq1227 eq12100
    | exact resolve eq12100 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12100
  have eq12138 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2004 eq12122
    | exact resolve eq12122 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq12122
  have eq12154 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq12138
       have i₂ := eq6309 sF0 x x
       grind)
    | (have i₁ := eq12138
       have i₂ := eq6309 sF0 x x
       grind)
    | exact superpose eq6309 eq12138
    | exact resolve eq12138 eq6309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12138
  have eq12206 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1540 eq638
    | (have j0 := eq638 (σ y) X1 X2
       grind)
    | exact resolve eq638 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq1540
  have eq12207 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1846 eq12206
    | exact resolve eq12206 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12206
  have eq12208 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq5349 eq12207
    | exact resolve eq12207 eq5349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349 eq12207
  have eq12364 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1111 eq12208
    | exact resolve eq12208 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq12208
  have eq12415 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq12364 x
       have i₂ := eq658 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq658 eq12364
    | exact resolve eq12364 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12364
  have eq12437 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq12415
       have i₂ := eq1227 sF4 sF2
       grind)
    | exact superpose eq1227 eq12415
    | exact resolve eq12415 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq12415
  have eq12453 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1919 eq12437
    | exact resolve eq12437 eq1919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919 eq12437
  have eq12469 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12453
       have i₂ := eq6309 sF4 sF2 x
       grind)
    | (have i₁ := eq12453
       have i₂ := eq6309 sF4 x sF2
       grind)
    | exact superpose eq6309 eq12453
    | exact resolve eq12453 eq6309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6309 eq12453
  have eq17401 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq646 X0 X1 x X3 X4
       have i₂ := eq658 X0 X1 x
       grind)
    | exact superpose eq658 eq646
    | exact resolve eq646 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq17519 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17401 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq17401
    | exact resolve eq17401 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq17401
  have eq17619 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17519 X0 X1 X2
       have i₂ := eq658 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq658 eq17519
    | exact resolve eq17519 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17519
  have eq17732 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17619 X0 X1 X2
       have i₂ := eq658 X0 X0 X0
       grind)
    | exact superpose eq658 eq17619
    | exact resolve eq17619 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17619
  have eq17804 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17732 X0 X1 X2
       have i₂ := eq6373 X0 X0 X1
       grind)
    | exact superpose eq6373 eq17732
    | exact resolve eq17732 eq6373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17732
  have eq17842 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq17804 X0 x X2
       have i₂ := eq658 X0 X0 x
       grind)
    | exact superpose eq658 eq17804
    | exact resolve eq17804 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17804
  have eq27993 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq781 X0 X1 x X3 X4 X5
       have i₂ := eq658 X0 X1 x
       grind)
    | exact superpose eq658 eq781
    | exact resolve eq781 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq38442 : (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (k x x) (M.op x x)) := by
    first
    | exact superpose eq49 eq561
    | exact resolve eq561 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq561
  have eq38494 : (k (M.op x x) (M.op x x)) = (τ (k (k (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq38442
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq38442
    | exact resolve eq38442 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38442
  have eq38510 : (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) = (k (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq38494
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq38494
    | exact resolve eq38494 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38494
  have eq38521 : (M.op (M.op x x) (M.op x x)) = (τ (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq38510
       have i₂ := eq66 (M.op x x)
       grind)
    | exact superpose eq66 eq38510
    | exact resolve eq38510 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38510
  have eq38532 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq38521
       have i₂ := eq66 (M.op sF2 sF2)
       grind)
    | exact superpose eq66 eq38521
    | exact resolve eq38521 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq38521
  have eq38543 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | (have i₁ := eq38532
       have i₂ := eq658 sF2 sF2 sF2
       grind)
    | exact superpose eq658 eq38532
    | exact resolve eq38532 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38532
  have eq38553 : (M.op (M.op x x) (M.op x x)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq6321 eq38543
    | exact resolve eq38543 eq6321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38543
  have eq38563 : (M.op (M.op x x) x) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq38553
       have i₂ := eq658 x x x
       grind)
    | exact superpose eq658 eq38553
    | exact resolve eq38553 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq38553
  have eq38567 : (M.op (M.op x y) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq38563
       have i₂ := eq6320 x
       grind)
    | exact superpose eq6320 eq38563
    | exact resolve eq38563 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38563
  have eq43503 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27993 X0 X0 X1 X2 X0
       have i₂ := eq17842 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)
       grind)
    | exact superpose eq17842 eq27993
    | exact resolve eq27993 eq17842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27993
  have eq43546 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43503 X0 X2 X2
       have i₂ := eq17842 X0 X2
       grind)
    | exact superpose eq17842 eq43503
    | exact resolve eq43503 eq17842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17842 eq43503
  have eq43628 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43546 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq43546
    | exact resolve eq43546 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43546
  have eq48754 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1233 (M.op (M.op x x) x)
       have i₂ := eq43628 x x x
       grind)
    | exact superpose eq43628 eq1233
    | exact resolve eq1233 eq43628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233 eq43628
  have eq49572 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op (M.op X0 X1) X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48754 X0
       have i₂ := eq4085 X0 X1
       grind)
    | (have i₁ := eq48754 X1
       have i₂ := eq4085 X1 X1
       grind)
    | exact superpose eq4085 eq48754
    | exact resolve eq48754 eq4085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4085 eq48754
  have eq57257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq57266 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq57257
    | exact resolve eq57257 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57257
  have eq57277 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq57266
       have r₂ := eq27
       grind)
    | exact resolve eq57266 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57266
  have eq57281 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq57277
    | exact resolve eq57277 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57277
  have eq57348 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57281 eq1201
    | exact resolve eq1201 eq57281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq57281
  have eq57367 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2910 eq57348
    | exact resolve eq57348 eq2910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2910 eq57348
  have eq57398 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57367 eq2906
    | exact resolve eq2906 eq57367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57367
  have eq57417 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq6321 eq57398
    | exact resolve eq57398 eq6321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6321 eq57398
  have eq57782 : (τ (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq57417 eq38567
    | exact resolve eq38567 eq57417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38567 eq57417
  have eq57863 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq57782
    | exact resolve eq57782 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57782
  have eq58970 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2906 y y
       have i₂ := eq57863
       grind)
    | exact superpose eq57863 eq2906
    | exact resolve eq2906 eq57863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57863
  have eq58987 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq2908 eq58970
    | exact resolve eq58970 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908 eq58970
  have eq59028 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | exact superpose eq58987 eq3587
    | exact resolve eq3587 eq58987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587 eq58987
  have eq59095 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq59028
  have eq59150 : y = (M.op (M.op x x) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2906 y x
       have i₂ := eq59095
       grind)
    | exact superpose eq59095 eq2906
    | exact resolve eq2906 eq59095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906
  have eq59162 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq49572 y x
       have i₂ := eq59095
       grind)
    | exact superpose eq59095 eq49572
    | exact resolve eq49572 eq59095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49572 eq59095
  have eq59165 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59162
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59162
    | exact resolve eq59162 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59162
  have eq59169 : y = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59150
       have i₂ := eq6320 x
       grind)
    | exact superpose eq6320 eq59150
    | exact resolve eq59150 eq6320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6320 eq59150
  have eq59174 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq59165
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq59165
    | exact resolve eq59165 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59165
  have eq59177 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1502 eq59174
    | exact resolve eq59174 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502 eq59174
  have eq59179 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1846 eq59177
    | exact resolve eq59177 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq59177
  have eq59243 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (M.op x y) X0) X0) y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59169 eq6373
    | exact resolve eq6373 eq59169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59169
  have eq59254 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12154 eq59243
    | exact resolve eq59243 eq12154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12154 eq59243
  have eq59471 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq59179 eq6373
    | exact resolve eq6373 eq59179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6373 eq59179
  have eq59480 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12469 eq59471
    | exact resolve eq59471 eq12469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12469 eq59471
  have eq59559 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq59254
       grind)
    | exact superpose eq59254 eq72
    | exact resolve eq72 eq59254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq59254
  have eq59744 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq59559
    | exact resolve eq59559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59559
  have eq61192 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq59744 eq59480
    | exact resolve eq59480 eq59744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59480 eq59744
  have eq61286 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq61192
  have eq61314 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq61286
       have r₂ := eq27
       grind)
    | exact resolve eq61286 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61286
  have eq61339 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq61314 eq29
    | exact resolve eq29 eq61314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61314
  have eq61523 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq61339
    | exact resolve eq61339 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq61339
  have eq61524 : x = y := by grind
  clear eq61523
  have eq61554 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq61524
       grind)
    | exact superpose eq61524 eq18
    | exact resolve eq18 eq61524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq61555 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq61524
       grind)
    | exact superpose eq61524 eq24
    | exact resolve eq24 eq61524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq61524
  have eq61744 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq61555
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61555
    | exact resolve eq61555 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq61555
  have eq61777 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq61744 eq26
    | exact resolve eq26 eq61744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq61744
  have eq62250 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq61777 eq71
    | exact resolve eq71 eq61777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq61777
  have eq62436 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq62250
       have i₂ := eq61554
       grind)
    | exact superpose eq61554 eq62250
    | exact resolve eq62250 eq61554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61554 eq62250
  have eq62467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62436 eq15
    | exact resolve eq15 eq62436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62436
  have eq62562 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq62467
    | exact resolve eq62467 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq62467
  have eq62588 : False := by grind
  exact eq62588

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_pyy_pyy_y_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k X0 X0) = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq10
    | exact resolve eq10 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq43
    | exact resolve eq43 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq70
    | exact resolve eq70 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq69
    | exact resolve eq69 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq101 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq16
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
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
  have eq239 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x X0)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x X0)) X1)) X2)) y) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq573 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) X2)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq581 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3 X2 X3
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq893 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq74 X1
       grind)
    | exact superpose eq74 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq912 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq893 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq893
    | (have j0 := eq893 y X0
       grind)
    | exact resolve eq893 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq1194 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) y) := by
    intro X0
    first
    | (have i₁ := eq593 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq593
    | (have j0 := eq593 x y X0
       grind)
    | exact resolve eq593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq593
    | (have j0 := eq593 (σ x) (σ y) X0
       grind)
    | exact resolve eq593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq593 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq593
    | (have j0 := eq593 x X0 y
       grind)
    | exact resolve eq593 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1211 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq593
    | (have j0 := eq593 (σ x) X0 (σ y)
       grind)
    | exact resolve eq593 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq593 X0 X1 x
       grind)
    | exact superpose eq593 eq14
    | exact resolve eq14 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1301 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1217 (σ X0) X1
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq1217
    | exact resolve eq1217 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1303 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1217 X0 (M.op X0 X1)
       have i₂ := eq593 X0 X0 X1
       grind)
    | exact superpose eq593 eq1217
    | exact resolve eq1217 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1217 (M.op X0 X1) X0
       grind)
    | exact superpose eq1217 eq55
    | exact resolve eq55 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1217 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1217 eq14
    | exact resolve eq14 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1338 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1308 X0 X1
       have i₂ := eq593 X0 X1 X1
       grind)
    | exact superpose eq593 eq1308
    | exact resolve eq1308 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1476 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1210 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1210
    | (have j0 := eq1210 y
       grind)
    | exact resolve eq1210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1536 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1476
       have i₂ := eq1194 X0
       grind)
    | exact superpose eq1194 eq1476
    | exact resolve eq1476 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1719 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1211
    | (have j0 := eq1211 (σ y)
       grind)
    | exact resolve eq1211 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1779 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1195 eq1719
    | exact resolve eq1719 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2110 : (M.op x x) = (M.op (M.op (M.op (M.op x x) (M.op x x)) (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1303 (M.op x x) y
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq1303
    | exact resolve eq1303 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2114 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq239 eq1303
    | exact resolve eq1303 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2116 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1719 eq1303
    | exact resolve eq1303 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2120 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq248 eq1303
    | exact resolve eq1303 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2161 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq2120
       have i₂ := eq1217 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1217 eq2120
    | exact resolve eq2120 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2165 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2116
       have i₂ := eq1217 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1217 eq2116
    | exact resolve eq2116 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116
  have eq2167 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2114
       have i₂ := eq1217 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1217 eq2114
    | exact resolve eq2114 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq2171 : (M.op x x) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq2110
       have i₂ := eq1217 x (M.op x x)
       grind)
    | exact superpose eq1217 eq2110
    | exact resolve eq2110 eq1217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217 eq2110
  have eq2214 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2161 eq248
    | exact resolve eq248 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq2227 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2161 eq593
    | exact resolve eq593 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2239 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq2227 x
       have i₂ := eq593 sF4 sF2 x
       grind)
    | exact superpose eq593 eq2227
    | exact resolve eq2227 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2246 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) := by
    first
    | exact superpose eq2161 eq2239
    | exact resolve eq2239 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2312 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq2167 eq239
    | exact resolve eq239 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq2326 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2167 eq593
    | exact resolve eq593 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2339 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | (have i₁ := eq2326 x
       have i₂ := eq593 sF0 x x
       grind)
    | exact superpose eq593 eq2326
    | exact resolve eq2326 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2326
  have eq2346 : (M.op (M.op (M.op x y) x) (M.op x y)) = (M.op (M.op (M.op x y) x) x) := by
    first
    | exact superpose eq2167 eq2339
    | exact resolve eq2339 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2546 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq2161 eq2165
    | exact resolve eq2165 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq2547 : (M.op x x) = (M.op x (M.op (M.op x y) x)) := by
    first
    | exact superpose eq2167 eq2171
    | exact resolve eq2171 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq3283 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1338 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1338
    | exact resolve eq1338 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3291 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1338 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1303 X0 X1
       grind)
    | exact superpose eq1303 eq1338
    | exact resolve eq1338 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3385 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3291 X0 X1
       have i₂ := eq1315 X0 X0
       grind)
    | exact superpose eq1315 eq3291
    | exact resolve eq3291 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq3291
  have eq3395 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3385 X0 X1
       have i₂ := eq593 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq593 eq3385
    | exact resolve eq3385 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3400 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3395 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq3395
    | exact resolve eq3395 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3395
  have eq3907 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3400 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3400
    | (have j0 := eq3400 x y
       grind)
    | exact resolve eq3400 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3913 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq3400
    | (have j0 := eq3400 (σ x) (σ y)
       grind)
    | exact resolve eq3400 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4060 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq3907 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq3907
       grind)
    | exact resolve eq12 eq3907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907
  have eq4077 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by grind
  clear eq4060
  have eq4230 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq3913 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq3913
       grind)
    | exact resolve eq12 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913
  have eq4247 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  clear eq4230
  have eq4657 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) y) := by
    intro X1
    first
    | exact superpose eq1536 eq243
    | (have j0 := eq243 y X1
       grind)
    | exact resolve eq243 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq4658 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) y) := by
    intro X1
    first
    | exact superpose eq2167 eq4657
    | exact resolve eq4657 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4657
  have eq4815 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3283 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3283 X0 X1
       grind)
    | exact superpose eq3283 eq3283
    | exact resolve eq3283 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4823 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq4658 eq3283
    | exact resolve eq3283 eq4658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658
  have eq4886 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3400 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq3283 X0 X1
       grind)
    | exact superpose eq3283 eq3400
    | exact resolve eq3400 eq3283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400
  have eq4887 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op (M.op (M.op X0 X1) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4886 X0 X1
       have i₂ := eq593 (M.op X0 X1) X1 X1
       grind)
    | exact superpose eq593 eq4886
    | exact resolve eq4886 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4886
  have eq4928 : ∀ X0 : G, (M.op x (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq2312 eq4823
    | exact resolve eq4823 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823
  have eq4932 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4815 X0 X1
       have i₂ := eq1338 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1338 eq4815
    | exact resolve eq4815 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4815
  have eq4946 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4887 X0 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq4887
    | exact resolve eq4887 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4887
  have eq4972 : ∀ X0 : G, (M.op x x) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0
    first
    | exact superpose eq2547 eq4928
    | exact resolve eq4928 eq2547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547 eq4928
  have eq4974 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4932 X0 X1
       have i₂ := eq593 X0 X0 X1
       grind)
    | exact superpose eq593 eq4932
    | exact resolve eq4932 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4932
  have eq5408 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1779 eq252
    | (have j0 := eq252 (σ y) X1
       grind)
    | exact resolve eq252 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq5409 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq2161 eq5408
    | exact resolve eq5408 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5489 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq5409 eq3283
    | exact resolve eq3283 eq5409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5409
  have eq5495 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq2214 eq5489
    | exact resolve eq5489 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5489
  have eq5505 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2546 eq5495
    | exact resolve eq5495 eq2546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546 eq5495
  have eq8002 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4974 X0 X2
       have i₂ := eq4974 X0 X1
       grind)
    | (have i₁ := eq4974 X1 X1
       have i₂ := eq4974 X1 X1
       grind)
    | exact superpose eq4974 eq4974
    | exact resolve eq4974 eq4974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8068 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1303 X0 X2
       have i₂ := eq4974 X0 X1
       grind)
    | (have i₁ := eq1303 X1 X1
       have i₂ := eq4974 X1 X1
       grind)
    | exact superpose eq4974 eq1303
    | exact resolve eq1303 eq4974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303 eq4974
  have eq10208 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq912 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq912
    | (have j0 := eq912 x
       grind)
    | exact resolve eq912 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq10246 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10208
       have i₂ := eq101
       grind)
    | exact superpose eq101 eq10208
    | exact resolve eq10208 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10208
  have eq10270 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq10246
    | exact resolve eq10246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10246
  have eq10283 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq10270
    | exact resolve eq10270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10270
  have eq10292 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq10283
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq10283
    | exact resolve eq10283 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10283
  have eq10300 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq10292
    | exact resolve eq10292 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10292
  have eq14262 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x (M.op (M.op (M.op x y) (M.op x y)) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq1536 eq572
    | (have j0 := eq572 y X1 X2
       grind)
    | exact resolve eq572 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1536
  have eq14263 : ∀ X1 X2 : G, (M.op x (M.op (M.op (M.op x y) x) X1)) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x (M.op (M.op (M.op x y) x) X1)) X2)) y) := by
    intro X1 X2
    first
    | exact superpose eq2167 eq14262
    | exact resolve eq14262 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14262
  have eq14264 : ∀ X2 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x x) X2)) y) := by
    intro X2
    first
    | exact superpose eq4972 eq14263
    | exact resolve eq14263 eq4972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4972 eq14263
  have eq14270 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op x X0))) y) := by
    intro X0
    first
    | (have i₁ := eq14264 y
       have i₂ := eq1194 X0
       grind)
    | exact superpose eq1194 eq14264
    | exact resolve eq14264 eq1194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194 eq14264
  have eq14327 : (M.op x x) = (M.op (M.op (M.op (M.op x y) (M.op x y)) x) y) := by
    first
    | (have i₁ := eq14270 x
       have i₂ := eq593 sF0 x (M.op x x)
       grind)
    | exact superpose eq593 eq14270
    | exact resolve eq14270 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14270
  have eq14351 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) y) := by
    first
    | (have i₁ := eq14327
       have i₂ := eq1338 sF0 x
       grind)
    | exact superpose eq1338 eq14327
    | exact resolve eq14327 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14327
  have eq14368 : (M.op x x) = (M.op (M.op (M.op (M.op x y) x) x) y) := by
    first
    | exact superpose eq2346 eq14351
    | exact resolve eq14351 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14351
  have eq14445 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq1779 eq573
    | (have j0 := eq573 (σ y) X1 X2
       grind)
    | exact resolve eq573 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq1779
  have eq14446 : ∀ X1 X2 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) X2)) (σ y)) := by
    intro X1 X2
    first
    | exact superpose eq2161 eq14445
    | exact resolve eq14445 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14445
  have eq14447 : ∀ X2 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ x)) X2)) (σ y)) := by
    intro X2
    first
    | exact superpose eq5505 eq14446
    | exact resolve eq14446 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5505 eq14446
  have eq14453 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) (σ y)) := by
    intro X0
    first
    | exact superpose eq1195 eq14447
    | exact resolve eq14447 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq14447
  have eq14510 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq14453 x
       have i₂ := eq593 sF4 sF2 (M.op sF2 x)
       grind)
    | exact superpose eq593 eq14453
    | exact resolve eq14453 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14453
  have eq14534 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq14510
       have i₂ := eq1338 sF4 sF2
       grind)
    | exact superpose eq1338 eq14510
    | exact resolve eq14510 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338 eq14510
  have eq14551 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2246 eq14534
    | exact resolve eq14534 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14534
  have eq14567 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14551
       have i₂ := eq8002 sF4 sF2 x
       grind)
    | (have i₁ := eq14551
       have i₂ := eq8002 sF4 x sF2
       grind)
    | exact superpose eq8002 eq14551
    | exact resolve eq14551 eq8002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002 eq14551
  have eq21564 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) = (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X3) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq581 X0 X1 x X3 X4
       have i₂ := eq593 X0 X1 x
       grind)
    | exact superpose eq593 eq581
    | exact resolve eq581 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq21684 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) (M.op (M.op X0 X0) (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21564 X0 (M.op X0 X1) X2 X2
       have i₂ := eq55 X0 X0 X1 X2
       grind)
    | exact superpose eq55 eq21564
    | exact resolve eq21564 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq21564
  have eq21799 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21684 X0 X1 X2
       have i₂ := eq593 (M.op X0 X0) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq593 eq21684
    | exact resolve eq21684 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21684
  have eq21923 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21799 X0 X1 X2
       have i₂ := eq593 X0 X0 X0
       grind)
    | exact superpose eq593 eq21799
    | exact resolve eq21799 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21799
  have eq22002 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21923 X0 X1 X2
       have i₂ := eq8068 X0 X0 X1
       grind)
    | exact superpose eq8068 eq21923
    | exact resolve eq21923 eq8068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8068 eq21923
  have eq22047 : ∀ X0 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op (M.op X0 X0) X0) X2) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq22002 X0 x X2
       have i₂ := eq593 X0 X0 x
       grind)
    | exact superpose eq593 eq22002
    | exact resolve eq22002 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22002
  have eq41915 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op (M.op (M.op (M.op X0 X0) X1) X3) X0) X4)) X5)) X3) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq702 X0 X1 x X3 X4 X5
       have i₂ := eq593 X0 X1 x
       grind)
    | exact superpose eq593 eq702
    | exact resolve eq702 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593 eq702
  have eq47830 : x = (M.op (M.op x x) y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq4077 eq2312
    | exact resolve eq2312 eq4077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4077
  have eq47952 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq47830
       have i₂ := eq1476
       grind)
    | exact superpose eq1476 eq47830
    | exact resolve eq47830 eq1476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476 eq47830
  have eq47967 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2167 eq47952
    | exact resolve eq47952 eq2167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167 eq47952
  have eq49558 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq4247 eq2214
    | exact resolve eq2214 eq4247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4247
  have eq49668 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1719 eq49558
    | exact resolve eq49558 eq1719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719 eq49558
  have eq49684 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2161 eq49668
    | exact resolve eq49668 eq2161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161 eq49668
  have eq62269 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41915 X0 X0 X1 X2 X0
       have i₂ := eq22047 X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)
       grind)
    | exact superpose eq22047 eq41915
    | exact resolve eq41915 eq22047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41915
  have eq62325 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
    intro X0 X1 X2
    by_contra hcon
    push Not at hcon
    have f62325_12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) (M.op X0 (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) X2))) X1) := by
      intro X0 X1 X2
      grind
    have f62325_13 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) X1) X0) = (M.op X0 X1) := by
      intro X0 X1
      grind
    have f62325_19 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f62325_22 : (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) ≠ (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by grind
    have f62325_23 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X0 X1) X2))) X1) := by
      intro X0 X1 X2
      first
      | (have i₁ := f62325_12 X0 X1 X2
         have i₂ := f62325_13 X0 X1
         grind)
      | exact superpose f62325_13 f62325_12
      | exact resolve f62325_12 f62325_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f62325_24 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
      intro X0 X1 X2
      first
      | (have i₁ := f62325_23 X0 X1 X2
         have i₂ := f62325_19 X0 X1 (M.op (M.op X0 X1) X2)
         grind)
      | exact superpose f62325_19 f62325_23
      | exact resolve f62325_23 f62325_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f62325_191 : X0 ≠ (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) := by
      first
      | (have i₁ := f62325_22
         have i₂ := f62325_19 X0 X1 (M.op (M.op X0 X1) X2)
         grind)
      | exact superpose f62325_19 f62325_22
      | exact resolve f62325_22 f62325_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f62325_192 : False := by
      first
      | (have r₁ := f62325_191
         have r₂ := f62325_24 X0 X1 X2
         grind)
      | exact resolve f62325_191 f62325_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f62325_192
  clear eq22047 eq62269
  have eq62432 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62325 X0 X1 X2
       have i₂ := eq14 X0 X1 (M.op (M.op X0 X1) X2)
       grind)
    | exact superpose eq14 eq62325
    | exact resolve eq62325 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62325
  have eq81022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq119 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq81023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq81022
    | exact resolve eq81022 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81022
  have eq81034 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq81023
       have r₂ := eq27
       grind)
    | exact resolve eq81023 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81023
  have eq81038 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq81034
    | exact resolve eq81034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81034
  have eq81042 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq81038
    | exact resolve eq81038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81038
  have eq81060 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq81042 eq3283
    | exact resolve eq3283 eq81042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81042
  have eq81077 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2246 eq81060
    | exact resolve eq81060 eq2246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2246 eq81060
  have eq89374 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq81077 eq62432
    | exact resolve eq62432 eq81077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62432 eq81077
  have eq89428 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq14567 eq89374
    | exact resolve eq89374 eq14567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14567 eq89374
  have eq89429 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq89428
  have eq89461 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq89429 eq79
    | (have r₁ := eq79
       have r₂ := eq89429
       grind)
    | exact resolve eq79 eq89429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq89429
  have eq89611 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq89461
  have eq113225 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq89611 eq4946
    | exact resolve eq4946 eq89611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89611
  have eq113238 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq2214 eq113225
    | exact resolve eq113225 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113225
  have eq113581 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq113238 eq115
    | exact resolve eq115 eq113238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq113238
  have eq113603 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq28 eq113581
    | exact resolve eq113581 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113581
  have eq113610 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq113603
       have r₂ := eq78
       grind)
    | exact resolve eq113603 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq113603
  have eq113613 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq113610
       grind)
    | exact superpose eq113610 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq113610
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq113610
       grind)
    | exact resolve eq13 eq113610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113629 : y = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq3283 y x
       have i₂ := eq113610
       grind)
    | exact superpose eq113610 eq3283
    | exact resolve eq3283 eq113610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3283 eq113610
  have eq113648 : y = (M.op (M.op (M.op x y) x) x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq2346 eq113629
    | exact resolve eq113629 eq2346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346 eq113629
  have eq113655 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have r₁ := eq113613
       have r₂ := eq18
       grind)
    | exact resolve eq113613 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113613
  have eq114427 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | exact superpose eq113648 eq14368
    | exact resolve eq14368 eq113648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14368 eq113648
  have eq117606 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq113655
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq113655
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq113655 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113655
  have eq117622 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq117606
  have eq117634 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117622
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117622
    | exact resolve eq117622 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117622
  have eq117637 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117634
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117634
    | exact resolve eq117634 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117634
  have eq117639 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq117637
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117637
    | exact resolve eq117637 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117637
  have eq119967 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    intro X0
    first
    | (have i₁ := eq1301 y X0
       have i₂ := eq114427
       grind)
    | exact superpose eq114427 eq1301
    | exact resolve eq1301 eq114427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114427
  have eq120084 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq119967 x
       have i₂ := eq1301 x x
       grind)
    | exact superpose eq1301 eq119967
    | exact resolve eq119967 eq1301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301 eq119967
  have eq120131 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq120084
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120084
    | exact resolve eq120084 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120084
  have eq120146 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq120131
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120131
    | exact resolve eq120131 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120131
  have eq120147 : x = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq120146
  have eq120156 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq120147
       grind)
    | exact superpose eq120147 eq101
    | exact resolve eq101 eq120147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq120147
  have eq120178 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120156
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120156
    | exact resolve eq120156 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120156
  have eq120187 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10300 eq120178
    | exact resolve eq120178 eq10300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10300 eq120178
  have eq175229 : y = (M.op (M.op (M.op x y) x) y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4946 y x
       have i₂ := eq117639
       grind)
    | exact superpose eq117639 eq4946
    | exact resolve eq4946 eq117639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117639
  have eq175243 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2312 eq175229
    | exact resolve eq175229 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312 eq175229
  have eq175263 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq175243
       grind)
    | exact superpose eq175243 eq73
    | exact resolve eq73 eq175243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175243
  have eq175531 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq175263
    | exact resolve eq175263 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175263
  have eq209324 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq120187 eq4946
    | exact resolve eq4946 eq120187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4946 eq120187
  have eq209338 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2214 eq209324
    | exact resolve eq209324 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214 eq209324
  have eq209339 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq209338
  have eq209425 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq209339 eq175531
    | exact resolve eq175531 eq209339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209558 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq209425
  have eq209627 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq209558
       have r₂ := eq27
       grind)
    | exact resolve eq209558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209558
  have eq210280 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209627 eq27
    | exact resolve eq27 eq209627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210358 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209627 eq49684
    | exact resolve eq49684 eq209627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49684 eq209627
  have eq210560 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210358
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq210358
    | exact resolve eq210358 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210358
  have eq210561 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq210560
  have eq217835 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq210561 eq175531
    | exact resolve eq175531 eq210561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175531 eq210561
  have eq217979 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq217835
  have eq218069 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq217979
       have r₂ := eq210280
       grind)
    | exact resolve eq217979 eq210280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210280 eq217979
  have eq218916 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq218069 eq29
    | exact resolve eq29 eq218069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218069
  have eq219155 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq218916
    | exact resolve eq218916 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218916
  have eq219156 : x = (M.op x y) ∨ x = y := by grind
  clear eq219155
  have eq219190 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq219156 eq20
    | exact resolve eq20 eq219156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219400 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq219156 eq47967
    | exact resolve eq47967 eq219156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47967 eq219156
  have eq219527 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq219400
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq219400
    | exact resolve eq219400 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq219400
  have eq219528 : x = (M.op x x) ∨ x = y := by grind
  clear eq219527
  have eq219697 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq219190
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq219190
    | exact resolve eq219190 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219190
  have eq220950 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq219528
       grind)
    | exact superpose eq219528 eq73
    | exact resolve eq73 eq219528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq219528
  have eq221261 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq220950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220950
    | exact resolve eq220950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220950
  have eq223938 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq221261 eq209339
    | exact resolve eq209339 eq221261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209339 eq221261
  have eq224080 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq223938
  have eq229687 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq224080 eq27
    | exact resolve eq27 eq224080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224080
  have eq230077 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq229687
       have r₂ := eq219697
       grind)
    | exact resolve eq229687 eq219697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219697 eq229687
  have eq230183 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq230077 eq29
    | exact resolve eq29 eq230077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq230077
  have eq230424 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq230183
    | exact resolve eq230183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq230183
  have eq230425 : x = y := by grind
  clear eq230424
  have eq230462 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq230425
       grind)
    | exact superpose eq230425 eq18
    | exact resolve eq18 eq230425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq230463 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq230425
       grind)
    | exact superpose eq230425 eq24
    | exact resolve eq24 eq230425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq230425
  have eq230953 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq230463
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq230463
    | exact resolve eq230463 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq230463
  have eq231027 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq230953 eq26
    | exact resolve eq26 eq230953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq230953
  have eq231715 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq231027 eq72
    | exact resolve eq72 eq231027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq231027
  have eq231996 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq231715
       have i₂ := eq230462
       grind)
    | exact superpose eq230462 eq231715
    | exact resolve eq231715 eq230462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230462 eq231715
  have eq232123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq231996 eq15
    | exact resolve eq15 eq231996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231996
  have eq232474 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq232123
    | exact resolve eq232123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq232123
  have eq232585 : False := by grind
  exact eq232585

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_x_pxy_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2666 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X3 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq66 (σ X0)
       grind)
    | exact superpose eq66 eq10
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq43
    | exact resolve eq43 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq70 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq49
    | exact resolve eq49 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq70
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq70
    | exact resolve eq70 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq69
    | exact resolve eq69 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq68
    | exact resolve eq68 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq77 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ x = (k x y) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq106 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq110 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq66 sF3
       grind)
    | exact superpose eq66 eq106
    | exact resolve eq106 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq112 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110
       have i₂ := eq66 y
       grind)
    | exact superpose eq66 eq110
    | exact resolve eq110 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq236 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq243 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq582 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq855 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq856 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq895 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq856 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq856
    | (have j0 := eq856 X0 y
       grind)
    | exact resolve eq856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq918 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq895 X0
       have i₂ := eq112
       grind)
    | exact superpose eq112 eq895
    | (have j0 := eq895 X0
       grind)
    | exact resolve eq895 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq895
  have eq1078 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq582
    | (have j0 := eq582 (σ x) (σ y) X0
       grind)
    | exact resolve eq582 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1092 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq582 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq582
    | (have j0 := eq582 x X0 y
       grind)
    | exact resolve eq582 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq582
    | (have j0 := eq582 (σ x) X0 (σ y)
       grind)
    | exact resolve eq582 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq582 X0 X1 x
       grind)
    | exact superpose eq582 eq14
    | exact resolve eq14 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1097 (σ X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1097
    | exact resolve eq1097 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1171 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1097 X0 (M.op X0 X1)
       have i₂ := eq582 X0 X0 X1
       grind)
    | exact superpose eq582 eq1097
    | exact resolve eq1097 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1176 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 X1 X0
       have i₂ := eq1097 (M.op X0 X1) X0
       grind)
    | exact superpose eq1097 eq55
    | exact resolve eq55 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op (M.op X0 X0) X1) X1
       have i₂ := eq1097 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq1097 eq14
    | exact resolve eq14 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1197 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1176 X0 X1
       have i₂ := eq582 X0 X1 X1
       grind)
    | exact superpose eq582 eq1176
    | exact resolve eq1176 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176
  have eq1285 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1092 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1092
    | (have j0 := eq1092 y
       grind)
    | exact resolve eq1092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1474 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq1093
    | (have j0 := eq1093 (σ y)
       grind)
    | exact resolve eq1093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1512 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1078 eq1474
    | exact resolve eq1474 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1783 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq236 eq1171
    | exact resolve eq1171 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1474 eq1171
    | exact resolve eq1171 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1789 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq243 eq1171
    | exact resolve eq1171 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1820 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1789
       have i₂ := eq1097 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1097 eq1789
    | exact resolve eq1789 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq1824 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1785
       have i₂ := eq1097 sF2 (M.op sF2 sF2)
       grind)
    | exact superpose eq1097 eq1785
    | exact resolve eq1785 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1826 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1783
       have i₂ := eq1097 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1097 eq1783
    | exact resolve eq1783 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1870 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1820 eq243
    | exact resolve eq243 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1956 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1826 eq236
    | exact resolve eq236 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2160 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    first
    | exact superpose eq1820 eq1824
    | exact resolve eq1824 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq2897 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1197 (M.op X0 X1) X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq1197
    | exact resolve eq1197 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2899 : x = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | exact superpose eq236 eq1197
    | exact resolve eq1197 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2901 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq243 eq1197
    | exact resolve eq1197 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq2905 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1197 (M.op (M.op X0 X0) X0) (M.op X0 X1)
       have i₂ := eq1171 X0 X1
       grind)
    | exact superpose eq1171 eq1197
    | exact resolve eq1197 eq1171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq2984 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2905 X0 X1
       have i₂ := eq1181 X0 X0
       grind)
    | exact superpose eq1181 eq2905
    | exact resolve eq2905 eq1181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1181 eq2905
  have eq2990 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2984 X0 X1
       have i₂ := eq582 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq582 eq2984
    | exact resolve eq2984 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984
  have eq2991 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2990 X0 X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq2990
    | exact resolve eq2990 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990
  have eq3441 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq2899 eq2991
    | exact resolve eq2991 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3456 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2991 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2991
    | (have j0 := eq2991 x y
       grind)
    | exact resolve eq2991 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3462 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq2991
    | (have j0 := eq2991 (σ x) (σ y)
       grind)
    | exact resolve eq2991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2991
  have eq3531 : (M.op (M.op (M.op x y) (M.op x y)) y) = (M.op (M.op (M.op x y) y) x) := by
    first
    | (have i₁ := eq3441
       have i₂ := eq582 sF0 y y
       grind)
    | exact superpose eq582 eq3441
    | exact resolve eq3441 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3441
  have eq3567 : x = (M.op (M.op (M.op x y) y) x) := by
    first
    | exact superpose eq236 eq3531
    | exact resolve eq3531 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq3531
  have eq3598 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq3456 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq3456
       grind)
    | exact resolve eq12 eq3456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq3611 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq3598
  have eq3615 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1826 eq3611
    | exact resolve eq3611 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611
  have eq3620 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3462 eq12
    | (have j0 := eq12 (σ x) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq3462
       grind)
    | exact resolve eq12 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3633 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq3620
  have eq3637 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1820 eq3633
    | exact resolve eq3633 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3633
  have eq4102 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2897 (M.op (M.op X0 X1) X1) (M.op X0 X1)
       have i₂ := eq2897 X0 X1
       grind)
    | exact superpose eq2897 eq2897
    | exact resolve eq2897 eq2897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4209 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X1)) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4102 X0 X1
       have i₂ := eq1197 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1197 eq4102
    | exact resolve eq4102 eq1197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197 eq4102
  have eq4247 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4209 X0 X1
       have i₂ := eq582 X0 X0 X1
       grind)
    | exact superpose eq582 eq4209
    | exact resolve eq4209 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq4209
  have eq4571 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1512 eq246
    | (have j0 := eq246 (σ y) X1
       grind)
    | exact resolve eq246 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq1512
  have eq4572 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ y)) := by
    intro X1
    first
    | exact superpose eq1820 eq4571
    | exact resolve eq4571 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4571
  have eq4679 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq4572 eq2897
    | exact resolve eq2897 eq4572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4572
  have eq4685 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq1870 eq4679
    | exact resolve eq4679 eq1870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4679
  have eq4693 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0
    first
    | exact superpose eq2160 eq4685
    | exact resolve eq4685 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160 eq4685
  have eq6773 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4247 X0 X2
       have i₂ := eq4247 X0 X1
       grind)
    | (have i₁ := eq4247 X1 X1
       have i₂ := eq4247 X1 X1
       grind)
    | exact superpose eq4247 eq4247
    | exact resolve eq4247 eq4247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4247
  have eq7351 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq918 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq918
    | (have j0 := eq918 x
       grind)
    | exact resolve eq918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq7381 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq7351
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq7351
    | exact resolve eq7351 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7351
  have eq7397 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq7381
    | exact resolve eq7381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7381
  have eq7409 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | exact superpose eq26 eq7397
    | exact resolve eq7397 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq7419 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7409
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq7409
    | exact resolve eq7409 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7409
  have eq7427 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq7419
    | exact resolve eq7419 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7419
  have eq9996 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op (M.op x y) y) X0) X0) := by
    intro X0
    first
    | exact superpose eq3567 eq6773
    | exact resolve eq6773 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567 eq6773
  have eq45306 : x = (M.op (M.op x x) y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq3615 eq1956
    | exact resolve eq1956 eq3615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1956 eq3615
  have eq45418 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq45306
       have i₂ := eq1285
       grind)
    | exact superpose eq1285 eq45306
    | exact resolve eq45306 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq45306
  have eq45431 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1826 eq45418
    | exact resolve eq45418 eq1826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826 eq45418
  have eq46014 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3637 eq1870
    | exact resolve eq1870 eq3637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870 eq3637
  have eq46114 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1474 eq46014
    | exact resolve eq46014 eq1474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1474 eq46014
  have eq46127 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1820 eq46114
    | exact resolve eq46114 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820 eq46114
  have eq52806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq52815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq52806
    | exact resolve eq52806 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52806
  have eq52826 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq52815
       have r₂ := eq27
       grind)
    | exact resolve eq52815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52815
  have eq52830 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq52826
    | exact resolve eq52826 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52826
  have eq52834 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq52830
    | exact resolve eq52830 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52830
  have eq52852 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq52834 eq1097
    | exact resolve eq1097 eq52834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52834
  have eq57096 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq52852 eq4693
    | exact resolve eq4693 eq52852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693 eq52852
  have eq57224 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq57096
    | exact resolve eq57096 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57096
  have eq57225 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq57224
  have eq57266 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57225 eq78
    | (have r₁ := eq78
       have r₂ := eq57225
       grind)
    | exact resolve eq78 eq57225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq57225
  have eq57369 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq57266
  have eq74682 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq57369 eq2897
    | exact resolve eq2897 eq57369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57369
  have eq74695 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2901 eq74682
    | exact resolve eq74682 eq2901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74682
  have eq75043 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq74695 eq59
    | exact resolve eq59 eq74695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq74695
  have eq75075 : x = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28 eq75043
    | exact resolve eq75043 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75043
  have eq75085 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq75075
       have r₂ := eq77
       grind)
    | exact resolve eq75075 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq75075
  have eq75110 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq1097 y X0
       have i₂ := eq75085
       grind)
    | exact superpose eq75085 eq1097
    | exact resolve eq1097 eq75085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097 eq75085
  have eq76556 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq75110 eq9996
    | exact resolve eq9996 eq75110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9996 eq75110
  have eq82894 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x x)) X0) X0) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq1168 y X0
       have i₂ := eq76556
       grind)
    | exact superpose eq76556 eq1168
    | exact resolve eq1168 eq76556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76556
  have eq82971 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq82894 x
       have i₂ := eq1168 x x
       grind)
    | exact superpose eq1168 eq82894
    | exact resolve eq82894 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq82894
  have eq83004 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq82971
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq82971
    | exact resolve eq82971 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82971
  have eq83014 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq83004
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83004
    | exact resolve eq83004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83004
  have eq83015 : x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq83014
  have eq83023 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq83015
       grind)
    | exact superpose eq83015 eq44
    | exact resolve eq44 eq83015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq83033 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq83015
       grind)
    | exact superpose eq83015 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq83015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83015
  have eq83049 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83033
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83033
    | exact resolve eq83033 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83033
  have eq83059 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83023
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq83023
    | exact resolve eq83023 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83023
  have eq83068 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83049
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83049
    | exact resolve eq83049 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83049
  have eq83079 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq83068
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq83068
    | exact resolve eq83068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83068
  have eq83139 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7427 eq83059
    | exact resolve eq83059 eq7427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7427 eq83059
  have eq144675 : y = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2897 y y
       have i₂ := eq83079
       grind)
    | exact superpose eq83079 eq2897
    | exact resolve eq2897 eq83079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83079
  have eq144691 : (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2899 eq144675
    | exact resolve eq144675 eq2899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2899 eq144675
  have eq144736 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq144691
       grind)
    | exact superpose eq144691 eq72
    | exact resolve eq72 eq144691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144691
  have eq144928 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq144736
    | exact resolve eq144736 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144736
  have eq156212 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq83139 eq2897
    | exact resolve eq2897 eq83139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897 eq83139
  have eq156231 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2901 eq156212
    | exact resolve eq156212 eq2901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2901 eq156212
  have eq156232 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq156231
  have eq156290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq156232 eq144928
    | exact resolve eq144928 eq156232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156383 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq156290
  have eq156433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq156383
       have r₂ := eq27
       grind)
    | exact resolve eq156383 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156383
  have eq157366 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq156433 eq27
    | exact resolve eq27 eq156433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157438 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq156433 eq46127
    | exact resolve eq46127 eq156433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46127 eq156433
  have eq157571 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq157438
       have i₂ := eq66 sF2
       grind)
    | exact superpose eq66 eq157438
    | exact resolve eq157438 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157438
  have eq157572 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq157571
  have eq166183 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq157572 eq144928
    | exact resolve eq144928 eq157572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144928 eq157572
  have eq166284 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq166183
  have eq166345 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq166284
       have r₂ := eq157366
       grind)
    | exact resolve eq166284 eq157366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157366 eq166284
  have eq166413 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq166345 eq29
    | exact resolve eq29 eq166345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166345
  have eq166629 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq166413
    | exact resolve eq166413 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166413
  have eq166630 : x = (M.op x y) ∨ x = y := by grind
  clear eq166629
  have eq166660 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq166630 eq20
    | exact resolve eq20 eq166630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166864 : x = (k x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq166630 eq45431
    | exact resolve eq45431 eq166630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45431 eq166630
  have eq166942 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq166864
       have i₂ := eq66 x
       grind)
    | exact superpose eq66 eq166864
    | exact resolve eq166864 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq166864
  have eq166943 : x = (M.op x x) ∨ x = y := by grind
  clear eq166942
  have eq167112 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq166660
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq166660
    | exact resolve eq166660 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166660
  have eq167566 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq166943
       grind)
    | exact superpose eq166943 eq72
    | exact resolve eq72 eq166943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq166943
  have eq167780 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq167566
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167566
    | exact resolve eq167566 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167566
  have eq170752 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq167780 eq156232
    | exact resolve eq156232 eq167780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156232 eq167780
  have eq170851 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq170752
  have eq179701 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq170851 eq27
    | exact resolve eq27 eq170851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170851
  have eq179998 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq179701
       have r₂ := eq167112
       grind)
    | exact resolve eq179701 eq167112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167112 eq179701
  have eq180068 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq179998 eq29
    | exact resolve eq29 eq179998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq179998
  have eq180286 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq180068
    | exact resolve eq180068 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq180068
  have eq180287 : x = y := by grind
  clear eq180286
  have eq180317 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq180287
       grind)
    | exact superpose eq180287 eq18
    | exact resolve eq18 eq180287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq180318 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq180287
       grind)
    | exact superpose eq180287 eq24
    | exact resolve eq24 eq180287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq180287
  have eq180770 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq180318
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180318
    | exact resolve eq180318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq180318
  have eq180830 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq180770 eq26
    | exact resolve eq26 eq180770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq180770
  have eq182483 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq180830 eq71
    | exact resolve eq71 eq180830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq180830
  have eq182685 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq182483
       have i₂ := eq180317
       grind)
    | exact superpose eq180317 eq182483
    | exact resolve eq182483 eq180317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180317 eq182483
  have eq182767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq182685 eq15
    | exact resolve eq15 eq182685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182685
  have eq183111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq182767
    | exact resolve eq182767 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq182767
  have eq183218 : False := by grind
  exact eq183218

/-- `Equation2666`: `x = ((x ◇ y) ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation2666 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2666 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2666.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3)) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X2)) X1 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ x = (k y x) := by
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
  have eq72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq213 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq218 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq700 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X0 X1 X2 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1049 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq700 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq700
    | (have j0 := eq700 x X0 y
       grind)
    | exact resolve eq700 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1050 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq27 eq700
    | (have j0 := eq700 (σ x) X0 (σ y)
       grind)
    | exact resolve eq700 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq700 X0 X1 x
       grind)
    | exact superpose eq700 eq14
    | exact resolve eq14 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1054 X0 (M.op X0 X1)
       have i₂ := eq700 X0 X0 X1
       grind)
    | exact superpose eq700 eq1054
    | exact resolve eq1054 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq1219 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq1049 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1049
    | (have j0 := eq1049 y
       grind)
    | exact resolve eq1049 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1390 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq27 eq1050
    | (have j0 := eq1050 (σ y)
       grind)
    | exact resolve eq1050 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1668 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq213 eq1118
    | exact resolve eq1118 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1674 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (σ x)) := by
    first
    | exact superpose eq218 eq1118
    | exact resolve eq1118 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1702 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq1674
       have i₂ := eq1054 sF4 (M.op sF4 sF4)
       grind)
    | exact superpose eq1054 eq1674
    | exact resolve eq1674 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1708 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1668
       have i₂ := eq1054 sF0 (M.op sF0 sF0)
       grind)
    | exact superpose eq1054 eq1668
    | exact resolve eq1668 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq1668
  have eq1749 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1702 eq218
    | exact resolve eq218 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1823 : x = (M.op (M.op (M.op x y) x) y) := by
    first
    | exact superpose eq1708 eq213
    | exact resolve eq213 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq33815 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33815
    | exact resolve eq33815 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33815
  have eq33828 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq33823
       have r₂ := eq28
       grind)
    | exact resolve eq33823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33823
  have eq33830 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq33828
    | exact resolve eq33828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33828
  have eq33835 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq33830 eq72
    | (have r₁ := eq72
       have r₂ := eq33830
       grind)
    | exact resolve eq72 eq33830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq33830
  have eq33918 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq33835
  have eq33919 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
  clear eq33918
  have eq33976 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq33919 eq104
    | exact resolve eq104 eq33919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq33979 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq33919 eq101
    | exact resolve eq101 eq33919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq33919
  have eq33989 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33976
  have eq33996 : x = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq33979
    | exact resolve eq33979 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33979
  have eq34004 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq33996
       have r₂ := eq71
       grind)
    | exact resolve eq33996 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq33996
  have eq34132 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq34004
       grind)
    | exact superpose eq34004 eq89
    | exact resolve eq89 eq34004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq34004
  have eq34162 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq34132
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34132
    | exact resolve eq34132 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34132
  have eq34217 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34162 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq34162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34162
  have eq34225 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq34217
  have eq34232 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq34225
    | exact resolve eq34225 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34225
  have eq34240 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq34232
    | exact resolve eq34232 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34232
  have eq34243 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq52
       have i₂ := eq33989
       grind)
    | exact superpose eq33989 eq52
    | exact resolve eq52 eq33989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33989
  have eq34386 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq34243
    | exact resolve eq34243 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34243
  have eq35119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq34240 eq34386
    | exact resolve eq34386 eq34240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35119
  have eq35222 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq35189
       have r₂ := eq28
       grind)
    | exact resolve eq35189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35189
  have eq35258 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35222 eq1749
    | exact resolve eq1749 eq35222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq35324 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1390 eq35258
    | exact resolve eq35258 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq35258
  have eq35337 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1702 eq35324
    | exact resolve eq35324 eq1702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1702 eq35324
  have eq36206 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq35222 eq35337
    | exact resolve eq35337 eq35222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35222 eq35337
  have eq36263 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36206
  have eq36636 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36263 eq34386
    | exact resolve eq34386 eq36263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34386 eq36263
  have eq36709 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq36636
  have eq36795 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq36709 eq30
    | exact resolve eq30 eq36709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36870 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq36795
    | exact resolve eq36795 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36795
  have eq36871 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq36870
  have eq36888 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq36871 eq29
    | exact resolve eq29 eq36871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36871
  have eq37013 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq36888
    | exact resolve eq36888 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36888
  have eq37075 : x = (M.op (M.op x x) y) ∨ x = y := by
    first
    | exact superpose eq37013 eq1823
    | exact resolve eq1823 eq37013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823
  have eq37154 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq37075
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq37075
    | exact resolve eq37075 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq37075
  have eq37213 : x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq1708 eq37154
    | exact resolve eq37154 eq1708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708 eq37154
  have eq37374 : x = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37013 eq37213
    | exact resolve eq37213 eq37013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37013 eq37213
  have eq37437 : x = (M.op x x) ∨ x = y := by grind
  clear eq37374
  have eq37714 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq52
       have i₂ := eq37437
       grind)
    | exact superpose eq37437 eq52
    | exact resolve eq52 eq37437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq37437
  have eq37865 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37714
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37714
    | exact resolve eq37714 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37714
  have eq38304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq37865 eq34240
    | exact resolve eq34240 eq37865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34240 eq37865
  have eq38379 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38304
  have eq40313 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq38379 eq28
    | exact resolve eq28 eq38379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38379
  have eq40414 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40313
       have r₂ := eq36709
       grind)
    | exact resolve eq40313 eq36709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36709 eq40313
  have eq40443 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq40414 eq30
    | exact resolve eq30 eq40414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq40414
  have eq40529 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq40443
    | exact resolve eq40443 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40443
  have eq40530 : x = y := by grind
  clear eq40529
  have eq40546 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq40530
       grind)
    | exact superpose eq40530 eq19
    | exact resolve eq19 eq40530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40547 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40530
       grind)
    | exact superpose eq40530 eq25
    | exact resolve eq25 eq40530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq40530
  have eq40702 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40547
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40547
    | exact resolve eq40547 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40547
  have eq40845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40702 eq27
    | exact resolve eq27 eq40702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40702
  have eq41135 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40845 eq70
    | exact resolve eq70 eq40845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq40845
  have eq41264 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq41135
       have i₂ := eq40546
       grind)
    | exact superpose eq40546 eq41135
    | exact resolve eq41135 eq40546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40546 eq41135
  have eq41287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41264 eq15
    | exact resolve eq15 eq41264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41264
  have eq41361 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq41287
    | exact resolve eq41287 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq41287
  have eq41385 : False := by grind
  exact eq41385

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X0 x) (M.op x x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq326 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X0) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq320 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq325 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq325 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq325 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq338 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq327 (σ X0)
       grind)
    | exact superpose eq327 eq15
    | exact resolve eq15 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq338 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq338
    | exact resolve eq338 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq338
  have eq409 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq67 (σ X0)
       have i₂ := eq357 X0
       grind)
    | exact superpose eq357 eq67
    | exact resolve eq67 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq616 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq326 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq617 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq616 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq629 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq617 X0 (τ X1)
       grind)
    | exact superpose eq617 eq18
    | (have j1 := eq617 X0 (τ X1)
       grind)
    | exact resolve eq18 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq617 (σ X0) (σ X1)
       grind)
    | exact superpose eq617 eq15
    | (have j1 := eq617 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq1202 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq629
    | exact resolve eq629 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq1285 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1202 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1202
    | (have j0 := eq1202 X0 X1
       grind)
    | exact resolve eq1202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq2686 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq632 x y
       grind)
    | exact superpose eq632 eq16
    | (have j1 := eq632 x y
       grind)
    | exact resolve eq16 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2741 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq2987 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2686
       have i₂ := eq1285 y x
       grind)
    | exact superpose eq1285 eq2686
    | (have j1 := eq1285 (σ y) (σ x)
       grind)
    | (have r₁ := eq2686
       have r₂ := eq1285 y x
       grind)
    | exact resolve eq2686 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686
  have eq2988 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2987
  have eq2993 : x ≠ x ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2988
       grind)
    | exact superpose eq2988 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2988
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2988
       grind)
    | exact resolve eq13 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2997 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq2988
       grind)
    | exact superpose eq2988 eq62
    | exact resolve eq62 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3002 : (k x y) = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2993
  have eq3003 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2997
       have i₂ := eq2988
       grind)
    | exact superpose eq2988 eq2997
    | exact resolve eq2997 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988 eq2997
  have eq3015 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq3003
  have eq3028 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq62 (σ y) (σ x)
       have i₂ := eq3015
       grind)
    | exact superpose eq3015 eq62
    | exact resolve eq62 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3095 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3028
       have i₂ := eq3015
       grind)
    | exact superpose eq3015 eq3028
    | exact resolve eq3028 eq3015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3015 eq3028
  have eq3111 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3095
  have eq3117 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3111
       have i₂ := eq357 x
       grind)
    | exact superpose eq357 eq3111
    | exact resolve eq3111 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111
  have eq3129 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq410 x
       have i₂ := eq3117
       grind)
    | exact superpose eq3117 eq410
    | exact resolve eq410 eq3117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3117
  have eq3167 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3129
       have i₂ := eq357 x
       grind)
    | exact superpose eq357 eq3129
    | exact resolve eq3129 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq3168 : (σ x) = (σ (M.op x x)) := by grind
  clear eq3167
  have eq249293 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2741 x y
       have i₂ := eq3002
       grind)
    | exact superpose eq3002 eq2741
    | (have j0 := eq2741 x y
       grind)
    | exact resolve eq2741 eq3002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741 eq3002
  have eq249311 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq249293
  have eq249317 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq249311
       have r₂ := eq3168
       grind)
    | exact resolve eq249311 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249311
  have eq249320 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq249317
       grind)
    | exact superpose eq249317 eq16
    | exact resolve eq16 eq249317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249342 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq249317
       grind)
    | exact superpose eq249317 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq249317
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq249317
       grind)
    | exact resolve eq13 eq249317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249317
  have eq249397 : (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq249342
  have eq249416 : (σ y) = (σ (M.op y y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq249397
       have i₂ := eq357 y
       grind)
    | exact superpose eq357 eq249397
    | exact resolve eq249397 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249397
  have eq249428 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq249416
       have i₂ := eq357 x
       grind)
    | exact superpose eq357 eq249416
    | exact resolve eq249416 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249416
  have eq249430 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq249428
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq249428
    | exact resolve eq249428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249428
  have eq249431 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq249430
       have i₂ := eq3168
       grind)
    | exact superpose eq3168 eq249430
    | exact resolve eq249430 eq3168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3168 eq249430
  have eq257962 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1285 y x
       have i₂ := eq249431
       grind)
    | exact superpose eq249431 eq1285
    | (have j0 := eq1285 y x
       grind)
    | exact resolve eq1285 eq249431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285 eq249431
  have eq258238 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq257962
       have r₂ := eq249320
       grind)
    | exact resolve eq257962 eq249320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257962
  have eq258381 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq249320
       have i₂ := eq258238
       grind)
    | exact superpose eq258238 eq249320
    | exact resolve eq249320 eq258238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249320 eq258238
  have eq258457 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq258381
  have eq258458 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq258457
  have eq258492 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq409 y X0
       have i₂ := eq258458
       grind)
    | exact superpose eq258458 eq409
    | (have j0 := eq409 y X0
       grind)
    | (have r₁ := eq409 y x
       have r₂ := eq258458
       grind)
    | exact resolve eq409 eq258458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258493 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq410 y
       have i₂ := eq258458
       grind)
    | exact superpose eq258458 eq410
    | exact resolve eq410 eq258458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq258458
  have eq258614 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq258492 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258492
  have eq258624 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq258493
       have i₂ := eq357 y
       grind)
    | exact superpose eq357 eq258493
    | exact resolve eq258493 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq258493
  have eq258625 : (σ y) = (σ (M.op y y)) := by grind
  clear eq258624
  have eq258626 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq258614 X0
       have j1 := eq409 y X0
       grind)
    | (have r₁ := eq258614 X0
       have r₂ := eq409 y x
       grind)
    | exact resolve eq258614 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq258614
  have eq258669 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq258625
       grind)
    | exact superpose eq258625 eq10
    | exact resolve eq10 eq258625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258625
  have eq258918 : y = (M.op y y) := by
    first
    | (have i₁ := eq258669
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq258669
    | exact resolve eq258669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258669
  have eq258979 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq258918
       grind)
    | exact superpose eq258918 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq258918
       grind)
    | exact resolve eq12 eq258918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258918
  have eq259116 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq258979 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258979
  have eq259695 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq258626 (σ X0)
       grind)
    | exact superpose eq258626 eq15
    | exact resolve eq15 eq258626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258626
  have eq259834 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq259695 X0
       have i₂ := eq259116 X0
       grind)
    | exact superpose eq259116 eq259695
    | exact resolve eq259695 eq259116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259116 eq259695
  have eq261521 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq259834 x
       grind)
    | exact superpose eq259834 eq16
    | (have r₁ := eq16
       have r₂ := eq259834 x
       grind)
    | exact resolve eq16 eq259834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259834
  have eq261751 : False := by grind
  exact eq261751

/-- `Equation2683`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2683 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2683 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2683.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq82 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq254 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq261 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq262 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq269 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq262
    | (have j0 := eq262 X0 X1
       grind)
    | exact resolve eq262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq270 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq865 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq270
    | exact resolve eq270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq16
    | (have j1 := eq270 x y
       grind)
    | exact resolve eq16 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq904 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq865 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq865
    | (have j0 := eq865 X0 X1
       grind)
    | exact resolve eq865 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq865
  have eq1001 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq904
    | exact resolve eq904 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq1148 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq873
       have i₂ := eq1001 x y
       grind)
    | exact superpose eq1001 eq873
    | (have j1 := eq1001 (σ x) (σ y)
       grind)
    | (have r₁ := eq873
       have r₂ := eq1001 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq873
       have r₂ := eq1001 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq873 eq1001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq1001
  have eq1151 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1148
  have eq1201 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1151
       grind)
    | exact superpose eq1151 eq10
    | exact resolve eq10 eq1151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq1239 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1201
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1201
    | exact resolve eq1201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1240 : x = y := by grind
  clear eq1239
  have eq1242 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq16
    | exact resolve eq16 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq1243 : False := by grind
  exact eq1243
