import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation2646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
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
  have eq1153 : (M.op x y) = (k x y) := by grind
  clear eq1114
  have eq1159 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1105
       have i₂ := eq1153
       grind)
    | exact superpose eq1153 eq1105
    | exact resolve eq1105 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq1153
  have eq1162 : False := by grind
  exact eq1162

/-- `Equation2646`: `x = ((x ◇ x) ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation2646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2646.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq18
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq28
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq28 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3345 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq502 X0 X1
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq502 X0 X1
       grind)
    | exact superpose eq502 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq502 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq502 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq502 X0 X1
       grind)
    | exact resolve eq13 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq3350 : ∀ X0 X1 : G, (M.op X0 (σ X1)) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3345 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3351 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3350 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq4949 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq3351 X0 X1
       grind)
    | exact superpose eq3351 eq28
    | (have j1 := eq3351 X0 X1
       grind)
    | exact resolve eq28 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3351
  have eq4988 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4949 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949
  have eq5005 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4988 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4988
    | exact resolve eq4988 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4988
  have eq5124 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5005 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq5005
    | (have j0 := eq5005 (τ (k X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact resolve eq5005 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5005
  have eq5166 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq5124 X1 X0
       grind)
    | exact superpose eq5124 eq11
    | (have j1 := eq5124 (k X0 X1) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq5124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5124
  have eq5290 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5166 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5166
    | (have j0 := eq5166 (M.op X0 X1) (k X0 X1)
       grind)
    | exact resolve eq5166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5166
  have eq5323 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq5290 X0 (τ X1)
       grind)
    | exact superpose eq5290 eq19
    | (have j1 := eq5290 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq5290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq5345 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5290 (σ X0) (σ X1)
       grind)
    | exact superpose eq5290 eq15
    | (have j1 := eq5290 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq5290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5290
  have eq5602 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5323 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5323
    | exact resolve eq5323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5323
  have eq5681 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5602 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5602
    | (have j0 := eq5602 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq5602 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5602
  have eq6101 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5345 x y
       grind)
    | exact superpose eq5345 eq16
    | (have j1 := eq5345 x y
       grind)
    | exact resolve eq16 eq5345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5345
  have eq6149 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6101
       have i₂ := eq5681 y x
       grind)
    | exact superpose eq5681 eq6101
    | (have j1 := eq5681 (σ x) (σ y)
       grind)
    | (have r₁ := eq6101
       have r₂ := eq5681 y x
       grind)
    | (have r₁ := eq6101
       have r₂ := eq5681 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq6101
       have r₂ := eq5681 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6101 eq5681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5681 eq6101
  have eq6152 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq6149
  have eq6155 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6152
       grind)
    | exact superpose eq6152 eq16
    | exact resolve eq16 eq6152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6152
  have eq6156 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6155
       have r₂ := eq22 x
       grind)
    | exact resolve eq6155 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6155
  have eq6157 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6156
       grind)
    | exact superpose eq6156 eq16
    | exact resolve eq16 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6158 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6156
       grind)
    | exact superpose eq6156 eq10
    | exact resolve eq10 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6216 : x = y := by
    first
    | (have i₁ := eq6158
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6158
    | exact resolve eq6158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6158
  have eq6217 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6157
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6157
    | exact resolve eq6157 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6157
  have eq6218 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6217
       have i₂ := eq6216
       grind)
    | exact superpose eq6216 eq6217
    | exact resolve eq6217 eq6216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216 eq6217
  have eq6219 : False := by grind
  exact eq6219

/-- `Equation2653`: `x = ((x ◇ x) ◇ (y ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_pyy_pxy_Equation2653 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2653 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2653.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq43 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have i₂ := eq9 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq144 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X0) X0) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq317 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq614 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = (M.op (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq148 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq147 X0 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq147 eq148
    | exact resolve eq148 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq148
  have eq618 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op (M.op X0 X0) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq614 X0
       have i₂ := eq144 X0
       grind)
    | exact superpose eq144 eq614
    | exact resolve eq614 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq688 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq9
    | exact resolve eq9 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq757 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X1 X1)) X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0
       have i₂ := eq688 X0 X1
       grind)
    | exact superpose eq688 eq144
    | exact resolve eq144 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq688
  have eq869 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq757 (M.op X0 X0) x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq757
    | exact resolve eq757 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq757 (σ (M.op X0 X0)) x
       have i₂ := eq48 X0 x
       grind)
    | exact superpose eq48 eq757
    | exact resolve eq757 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq757
  have eq2472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq317
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq317
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq317
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq317
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq317 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq2473 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2472
  have eq40617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2473
       grind)
    | exact superpose eq2473 eq16
    | exact resolve eq16 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq40618 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq40617
       have r₂ := eq23 x
       grind)
    | exact resolve eq40617 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40617
  have eq40620 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40618
       grind)
    | exact superpose eq40618 eq10
    | exact resolve eq10 eq40618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40618
  have eq40733 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq40620
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40620
    | exact resolve eq40620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40620
  have eq40754 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40733
       grind)
    | exact superpose eq40733 eq16
    | exact resolve eq16 eq40733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40733
  have eq40755 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq40754
       have r₂ := eq23 x
       grind)
    | exact resolve eq40754 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq40754
  have eq41051 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq40755
       grind)
    | exact superpose eq40755 eq10
    | exact resolve eq10 eq40755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40755
  have eq41202 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41051
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq41051
    | exact resolve eq41051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41051
  have eq41203 : y = (M.op x x) := by grind
  clear eq41202
  have eq41405 : y = (M.op x y) := by
    first
    | (have i₁ := eq869 x
       have i₂ := eq41203
       grind)
    | exact superpose eq41203 eq869
    | exact resolve eq869 eq41203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq41406 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq871 x
       have i₂ := eq41203
       grind)
    | exact superpose eq41203 eq871
    | exact resolve eq871 eq41203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871 eq41203
  have eq43560 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq41406
       grind)
    | exact superpose eq41406 eq16
    | exact resolve eq16 eq41406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41406
  have eq43590 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq43560
       have i₂ := eq41405
       grind)
    | exact superpose eq41405 eq43560
    | exact resolve eq43560 eq41405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41405 eq43560
  have eq43591 : False := by grind
  exact eq43591

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyy_y_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X1 : G, (k X1 (M.op X1 X1)) = X1 ∨ (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq21 X1 X0
       grind)
    | exact superpose eq21 eq10
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq67 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 ∨ (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq19 X1
       have i₂ := eq66 X1
       grind)
    | exact superpose eq66 eq19
    | (have j0 := eq19 X1
       grind)
    | exact resolve eq19 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq69 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq66 (τ X0)
       grind)
    | exact superpose eq66 eq20
    | exact resolve eq20 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (M.op (M.op X0 X0) (M.op X1 X2)) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op X2 X3)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X2 X3
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq21
    | (have j1 := eq67 (τ X0)
       grind)
    | exact resolve eq21 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq77 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq77
    | (have j0 := eq77 X0
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq65
    | exact resolve eq65 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X0) X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq9
    | exact resolve eq9 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)
       have i₂ := eq82 (M.op X0 X0)
       grind)
    | exact superpose eq82 eq9
    | exact resolve eq9 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq88 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq65 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq65 eq87
    | exact resolve eq87 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq89 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq88
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op (M.op X0 X0) X0) (M.op X0 X0)
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq70
    | exact resolve eq70 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq89
  have eq118 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X1 (M.op (M.op X0 X0) X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq83
    | exact resolve eq83 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op X1 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) X0)) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq66 (M.op (M.op X0 X0) X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq66
    | exact resolve eq66 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (M.op (M.op X0 X0) X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq96
    | exact resolve eq96 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op (M.op X2 X2) X2)
       have i₂ := eq83 X2 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq140 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq131 X0
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq131
    | exact resolve eq131 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq131
  have eq164 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X3 X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq130 X0 X3 X4
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq130
    | exact resolve eq130 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (M.op X0 X1) X0 X1
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq130
    | exact resolve eq130 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X1
       have i₂ := eq130 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq130 eq9
    | exact resolve eq9 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq135 X0 X3
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq135
    | exact resolve eq135 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq179 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op (M.op X0 (M.op X1 X2)) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140 X0
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq140
    | exact resolve eq140 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq72
    | exact resolve eq72 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X2)) = (M.op X0 (M.op X0 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 (M.op X0 (M.op (M.op X0 X1) X2)) X0 X1
       have i₂ := eq180 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq241 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq263 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X0)) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq137 (M.op (M.op X0 X0) X0) X1 X2
       have i₂ := eq137 X0 X0 X0
       grind)
    | exact superpose eq137 eq137
    | exact resolve eq137 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 (M.op (M.op X0 X0) X2) (M.op (M.op X2 X2) x)
       have i₂ := eq137 X2 X0 x
       grind)
    | exact superpose eq137 eq180
    | exact resolve eq180 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op X0 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3)) (M.op X0 X1) X2
       have i₂ := eq178 X0 (M.op (M.op X0 X1) X2) X3 X1
       grind)
    | exact superpose eq178 eq180
    | exact resolve eq180 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op (M.op X0 (M.op X1 X2)) X1)) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 (M.op (M.op X0 (M.op X1 X2)) X1) X0 x
       have i₂ := eq178 X0 X1 X2 x
       grind)
    | exact superpose eq178 eq130
    | exact resolve eq130 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X0 (M.op X1 X2))) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq532 X0 X1 X2
       have i₂ := eq65 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq65 eq532
    | exact resolve eq532 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq557 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X0 (M.op X1 X2))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq543 X0 X1 X2
       have i₂ := eq173 (M.op X0 (M.op X1 X2)) X1
       grind)
    | exact superpose eq173 eq543
    | exact resolve eq543 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq543
  have eq561 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq557 X0 X1 X2
       have i₂ := eq178 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq178 eq557
    | exact resolve eq557 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq223 X0 X1 X2
       have i₂ := eq561 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq561 eq223
    | exact resolve eq223 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq563 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq528 X0 X1 X2 X3
       have i₂ := eq561 X0 (M.op (M.op X0 X1) X2) X3
       grind)
    | exact superpose eq561 eq528
    | exact resolve eq528 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq643 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq561 X1 (M.op (M.op X0 x) (M.op (M.op x x) x)) X0
       have i₂ := eq288 x X0 x
       grind)
    | exact superpose eq288 eq561
    | exact resolve eq561 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq848 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq241 x y
       grind)
    | exact superpose eq241 eq16
    | (have j1 := eq241 x y
       grind)
    | exact resolve eq16 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X2)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq241 X0 X0
       grind)
    | exact superpose eq241 eq9
    | (have j1 := eq241 X0 X0
       grind)
    | exact resolve eq9 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq871 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq241 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq872 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq883 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ (k X0 X0)) (M.op X1 X2)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq849 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq981 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq563 (M.op X0 X1) (M.op (M.op X1 X1) x) X0 X3
       have i₂ := eq288 X1 X0 x
       grind)
    | exact superpose eq288 eq563
    | exact resolve eq563 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288 eq563
  have eq1025 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq981 X0 X1 X3
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq981
    | exact resolve eq981 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq981
  have eq1388 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X3 X4)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq74 X0 X0 X3 X4
       have i₂ := eq130 X0 X1 X2
       grind)
    | exact superpose eq130 eq74
    | exact resolve eq74 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq1410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 (M.op (M.op X0 X1) X2) (M.op X0 X1) X0 X1
       have i₂ := eq74 (M.op X0 X1) X2 (M.op X0 X1) X2
       grind)
    | exact superpose eq74 eq74
    | exact resolve eq74 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1522 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (τ X0) (τ X0))) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq872 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq872
    | exact resolve eq872 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq1564 : ∀ X0 : G, (k (σ (τ X0)) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1522 X0
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq1522
    | (have j0 := eq1522 X0
       grind)
    | exact resolve eq1522 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1569 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq1564 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1564
    | (have j0 := eq1564 X0
       grind)
    | exact resolve eq1564 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1643 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X1 X0) X0) X1) ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq179 X1 X0 X0
       have i₂ := eq1569 X0
       grind)
    | exact superpose eq1569 eq179
    | (have j1 := eq1569 X0
       grind)
    | exact resolve eq179 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2417 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X2) X1) (M.op (M.op X0 X0) X0)) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74 X1 X2 (M.op X0 X3) (M.op (M.op X3 X3) X3)
       have i₂ := eq118 X0 X3
       grind)
    | exact superpose eq118 eq74
    | exact resolve eq74 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2572 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq1569 (τ X0)
       grind)
    | exact superpose eq1569 eq69
    | (have j1 := eq1569 (τ X0)
       grind)
    | exact resolve eq69 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2610 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq2572 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2572
    | (have j0 := eq2572 X0
       grind)
    | exact resolve eq2572 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2611 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2610 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq2610
    | (have j0 := eq2610 X0
       grind)
    | exact resolve eq2610 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq2954 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq176 (M.op X0 X0) (M.op (M.op X1 X2) X3) X1 X2
       have i₂ := eq9 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq9 eq176
    | exact resolve eq176 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2962 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X0)) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op (M.op X0 X1) X0) (M.op (M.op X2 X3) X4) X2 X3
       have i₂ := eq74 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq74 eq176
    | exact resolve eq176 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq176
  have eq3064 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2962 X0 X1 X2 X3 X4
       have i₂ := eq1025 (M.op X0 X1) X2 X0
       grind)
    | exact superpose eq1025 eq2962
    | exact resolve eq2962 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2962
  have eq3072 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2954 X0 X1 X2 X3
       have i₂ := eq1025 X0 X1 X0
       grind)
    | exact superpose eq1025 eq2954
    | exact resolve eq2954 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954
  have eq3111 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X2 X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3064 X0 X1 X2 X3 X4
       have i₂ := eq1410 X0 X1 X2
       grind)
    | exact superpose eq1410 eq3064
    | exact resolve eq3064 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq3064
  have eq3116 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X1) (M.op X0 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq263 X0 X1 X2
       have i₂ := eq3072 X1 X0 X0 X0
       grind)
    | exact superpose eq3072 eq263
    | exact resolve eq263 eq3072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq3072
  have eq3157 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X1) (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2417 X0 X1 X2 X3
       have i₂ := eq3111 X1 X2 X0 X0 X0
       grind)
    | exact superpose eq3111 eq2417
    | exact resolve eq2417 eq3111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417 eq3111
  have eq3225 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3116 X1 (M.op X0 (M.op X1 X3)) X2
       have i₂ := eq178 X0 X1 X3 (M.op X1 X3)
       grind)
    | exact superpose eq178 eq3116
    | exact resolve eq3116 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq3288 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq3116 X2 X0 x
       grind)
    | exact superpose eq3116 eq9
    | exact resolve eq9 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3300 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 X2) X0)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X1 (M.op (M.op X0 X2) X0) (M.op X2 x)
       have i₂ := eq3116 X2 X0 x
       grind)
    | exact superpose eq3116 eq180
    | exact resolve eq180 eq3116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3480 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X0) X0)) = (M.op X1 (M.op (M.op X0 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3225 X1 (M.op X0 X2) X3 (M.op (M.op X2 X2) X2)
       have i₂ := eq118 X0 X2
       grind)
    | exact superpose eq118 eq3225
    | exact resolve eq3225 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq4153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3225 (M.op (M.op X0 X0) X1) (M.op X1 X2) X3 X1
       have i₂ := eq3288 X1 X0 X2
       grind)
    | exact superpose eq3288 eq3225
    | exact resolve eq3225 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq4373 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3300 X1 X0 X2
       have i₂ := eq3225 (M.op X0 X1) (M.op X1 X2) X1 X3
       grind)
    | (have i₁ := eq3300 X1 X0 X2
       have i₂ := eq3225 (M.op X0 X1) (M.op X1 X2) X3 X1
       grind)
    | exact superpose eq3225 eq3300
    | exact resolve eq3300 eq3225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300
  have eq5313 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq69
    | (have j1 := eq80 X0
       grind)
    | exact resolve eq69 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq5317 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140 (τ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq140
    | (have j1 := eq80 X0
       grind)
    | exact resolve eq140 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq5318 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq72
    | (have j1 := eq80 X0
       grind)
    | exact resolve eq72 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5369 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5317 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq5317
    | (have j0 := eq5317 X0
       grind)
    | exact resolve eq5317 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5317
  have eq5370 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5313 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5313
    | (have j0 := eq5313 X0
       grind)
    | exact resolve eq5313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5313
  have eq5378 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq5318 eq5369
    | (have j0 := eq5369 X0
       have j1 := eq5318 X0
       grind)
    | exact resolve eq5369 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5369
  have eq5379 : ∀ X0 : G, (k X0 (σ (τ X0))) = X0 ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq5318 eq5370
    | (have j0 := eq5370 X0
       have j1 := eq5318 X0
       grind)
    | exact resolve eq5370 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5318 eq5370
  have eq5385 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5379 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5379
    | (have j0 := eq5379 X0
       grind)
    | exact resolve eq5379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5379
  have eq5676 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 ∨ (k X0 X0) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4153 X0 X1 X2 X3
       have i₂ := eq1569 X0
       grind)
    | exact superpose eq1569 eq4153
    | (have j1 := eq1569 X0
       grind)
    | exact resolve eq4153 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7004 : ∀ X0 : G, (k (σ (τ X0)) X0) = X0 ∨ (k X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5385 X0
       have i₂ := eq1569 (τ X0)
       grind)
    | exact superpose eq1569 eq5385
    | (have j0 := eq5385 X0
       have j1 := eq1569 (τ X0)
       grind)
    | (have r₁ := eq5385 X0
       have r₂ := eq1569 X0
       grind)
    | exact resolve eq5385 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569 eq5385
  have eq7044 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7004 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7004
    | (have j0 := eq7004 X0
       grind)
    | exact resolve eq7004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7045 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ X0) ≠ (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq7044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7044
  have eq7059 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7045 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq7045
    | (have j0 := eq7045 X0
       grind)
    | exact resolve eq7045 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7045
  have eq7070 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7059 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq7059
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq7059 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7072 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7059 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq7059
    | exact resolve eq7059 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7059
  have eq7079 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq7070 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7070
  have eq7169 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op (k (σ (τ X0)) X0) (M.op X1 X2)) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq883 (τ X0) X1 X2
       have i₂ := eq21 X0 (τ X0)
       grind)
    | exact superpose eq21 eq883
    | (have j0 := eq883 (τ X0) X1 X2
       grind)
    | exact resolve eq883 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq883
  have eq7339 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) (M.op X1 X2)) X1) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7169 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7169
    | (have j0 := eq7169 X0 X1 X2
       grind)
    | exact resolve eq7169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7169
  have eq7356 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) (M.op X1 X2)) X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7339 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7339
    | (have j0 := eq7339 X0 X1 X2
       grind)
    | exact resolve eq7339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7339
  have eq8088 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3157 (M.op (M.op X1 X2) X3) X0 X1 X4
       have i₂ := eq4373 X0 X1 X2 X3
       grind)
    | exact superpose eq4373 eq3157
    | exact resolve eq3157 eq4373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3157 eq4373
  have eq11681 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op (M.op X1 X4) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3480 X1 X0 X4 X5
       have i₂ := eq3480 X1 X0 X2 X3
       grind)
    | (have i₁ := eq3480 X3 X1 X2 X3
       have i₂ := eq3480 X3 X1 X3 X3
       grind)
    | exact superpose eq3480 eq3480
    | exact resolve eq3480 eq3480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3480
  have eq22426 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X0 (M.op (M.op (k X0 X0) X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3116 (M.op (k X0 X0) X1) (k X0 X0) X2
       have i₂ := eq7356 X0 (k X0 X0) X1
       grind)
    | exact superpose eq7356 eq3116
    | (have j1 := eq7356 X0 X1 X2
       grind)
    | exact resolve eq3116 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq22455 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (k X0 X0) X2) X3)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq11681 X1 (k X0 X0) X2 X3 (M.op x x) x
       have i₂ := eq7356 X0 x x
       grind)
    | exact superpose eq7356 eq11681
    | (have j1 := eq7356 X0 X1 X2
       grind)
    | exact resolve eq11681 eq7356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7356 eq11681
  have eq22600 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq22455 eq22426
    | (have j0 := eq22426 X0 x x
       have j1 := eq22455 X0 x x x
       grind)
    | exact resolve eq22426 eq22455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22426 eq22455
  have eq22743 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq22600 (τ X0)
       grind)
    | exact superpose eq22600 eq34
    | (have j1 := eq22600 (τ X0)
       grind)
    | exact resolve eq34 eq22600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22600
  have eq25429 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq7072 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq7072
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq7072 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7072
  have eq25438 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25429 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25429
  have eq25446 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq25438 X0
       have j1 := eq7079 X0
       grind)
    | (have r₁ := eq25438 X0
       have r₂ := eq7079 X0
       grind)
    | exact resolve eq25438 eq7079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7079 eq25438
  have eq26085 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) ≠ (k (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1643 (τ X0) (τ X0)
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq1643
    | (have j0 := eq1643 (τ X0) x
       have j1 := eq80 X0
       grind)
    | exact resolve eq1643 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1643
  have eq26137 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) ≠ (k (τ X0) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26085 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq26085
    | (have j0 := eq26085 X0
       grind)
    | exact resolve eq26085 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26085
  have eq26211 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26137 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq26137
    | (have j0 := eq26137 X0
       grind)
    | exact resolve eq26137 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26137
  have eq26258 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq26211 X0
       have j1 := eq5378 X0
       grind)
    | (have r₁ := eq26211 X0
       have r₂ := eq5378 X0
       grind)
    | exact resolve eq26211 eq5378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5378 eq26211
  have eq26289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (σ (τ X0)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq22743 eq26258
    | (have j0 := eq26258 X0
       have j1 := eq22743 X0
       grind)
    | exact resolve eq26258 eq22743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22743 eq26258
  have eq26303 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq26289 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26289
    | (have j0 := eq26289 X0
       grind)
    | exact resolve eq26289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26289
  have eq26308 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26303 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26303
    | (have j0 := eq26303 (σ X0)
       grind)
    | exact resolve eq26303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26303
  have eq26462 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26308 X0
       have i₂ := eq25 (σ X0) X0
       grind)
    | exact superpose eq25 eq26308
    | (have j0 := eq26308 X0
       grind)
    | exact resolve eq26308 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq26308
  have eq26475 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26462 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq26462
    | (have j0 := eq26462 X0
       grind)
    | exact resolve eq26462 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26462
  have eq26479 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq26475 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq26475
    | (have j0 := eq26475 X0
       grind)
    | exact resolve eq26475 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26475
  have eq27097 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq26479 X0
       grind)
    | exact superpose eq26479 eq10
    | (have j1 := eq26479 X0
       grind)
    | exact resolve eq10 eq26479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26479
  have eq27140 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq27097 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27097
    | (have j0 := eq27097 X0
       grind)
    | exact resolve eq27097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27097
  have eq27184 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq27140 (τ X0)
       grind)
    | exact superpose eq27140 eq20
    | (have j1 := eq27140 (τ X0)
       grind)
    | exact resolve eq20 eq27140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27188 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have j0 := eq27140 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27140
  have eq27192 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq27184 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq27184
    | (have j0 := eq27184 X0
       grind)
    | exact resolve eq27184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27184
  have eq27217 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq27192 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq27192
    | (have j0 := eq27192 X0
       grind)
    | exact resolve eq27192 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27192
  have eq27235 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq27217 X0
       have j1 := eq2611 X0
       grind)
    | (have r₁ := eq27217 X0
       have r₂ := eq2611 X0
       grind)
    | exact resolve eq27217 eq2611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611 eq27217
  have eq27365 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 (σ X0)
       have i₂ := eq27188 (σ X0)
       grind)
    | exact superpose eq27188 eq31
    | (have j1 := eq27188 (σ X0)
       grind)
    | exact resolve eq31 eq27188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27188
  have eq27382 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27365 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27365
    | (have j0 := eq27365 X0
       grind)
    | exact resolve eq27365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27365
  have eq27405 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27235 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq27235
    | exact resolve eq27235 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27418 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq27235 X0
       grind)
    | exact superpose eq27235 eq10
    | exact resolve eq10 eq27235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27235
  have eq27590 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27405 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq27405
    | exact resolve eq27405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27405
  have eq27916 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq27590 X0
       grind)
    | exact superpose eq27590 eq10
    | exact resolve eq10 eq27590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27590
  have eq27956 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq27916 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq27916
    | exact resolve eq27916 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27916
  have eq28111 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5676 X0 X1 X2 X3
       have i₂ := eq27956 X0
       grind)
    | exact superpose eq27956 eq5676
    | (have j0 := eq5676 X0 X1 X2 X3
       grind)
    | exact resolve eq5676 eq27956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5676
  have eq28386 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq27382 X0
       have i₂ := eq27956 X0
       grind)
    | exact superpose eq27956 eq27382
    | (have j0 := eq27382 X0
       grind)
    | exact resolve eq27382 eq27956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27382
  have eq28387 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27418 X0
       have i₂ := eq27956 X0
       grind)
    | exact superpose eq27956 eq27418
    | exact resolve eq27418 eq27956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27418
  have eq29310 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq27956 (σ X0)
       grind)
    | exact superpose eq27956 eq15
    | exact resolve eq15 eq27956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29329 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29310 X0
       have i₂ := eq27956 X0
       grind)
    | exact superpose eq27956 eq29310
    | exact resolve eq29310 eq27956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27956 eq29310
  have eq29521 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq28386 X0
       have i₂ := eq29329 X0
       grind)
    | exact superpose eq29329 eq28386
    | (have j0 := eq28386 X0
       grind)
    | exact resolve eq28386 eq29329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28386
  have eq29592 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq848
       have i₂ := eq29329 x
       grind)
    | exact superpose eq29329 eq848
    | exact resolve eq848 eq29329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq29629 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq29592
       have i₂ := eq29329 y
       grind)
    | exact superpose eq29329 eq29592
    | exact resolve eq29592 eq29329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29592
  have eq29802 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq66 (τ X0)
       have i₂ := eq28387 X0
       grind)
    | exact superpose eq28387 eq66
    | exact resolve eq66 eq28387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29804 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq28387 X0
       grind)
    | exact superpose eq28387 eq72
    | exact resolve eq72 eq28387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29847 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq643 (τ X0) (τ X0)
       have i₂ := eq28387 X0
       grind)
    | exact superpose eq28387 eq643
    | exact resolve eq643 eq28387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29905 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29802 X0
       have i₂ := eq34 (M.op X0 X0) X0
       grind)
    | exact superpose eq34 eq29802
    | exact resolve eq29802 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq29802
  have eq29939 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29905 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq29905
    | exact resolve eq29905 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29905
  have eq29975 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op (M.op X0 X0) X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq29804 X0
       have i₂ := eq29939 X0
       grind)
    | exact superpose eq29939 eq29804
    | exact resolve eq29804 eq29939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29804 eq29939
  have eq30023 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq66 (σ X0)
       have i₂ := eq29329 X0
       grind)
    | exact superpose eq29329 eq66
    | exact resolve eq66 eq29329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30068 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq643 (σ X0) (σ X0)
       have i₂ := eq29329 X0
       grind)
    | exact superpose eq29329 eq643
    | exact resolve eq643 eq29329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29329
  have eq30138 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30023 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq30023
    | exact resolve eq30023 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30023
  have eq30160 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq30138 X0
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq30138
    | exact resolve eq30138 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq30138
  have eq30436 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (τ (M.op X0 X0))) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29521 (τ X0)
       have i₂ := eq28387 X0
       grind)
    | exact superpose eq28387 eq29521
    | exact resolve eq29521 eq28387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29521
  have eq30438 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (τ X0)) ∨ (τ X0) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30436 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq30436
    | (have j0 := eq30436 X0
       grind)
    | exact resolve eq30436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30436
  have eq30457 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq30438 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30438
    | (have j0 := eq30438 X0
       grind)
    | exact resolve eq30438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30438
  have eq30873 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op (M.op X0 X0) X0))) = (M.op (τ X0) (M.op (τ (M.op (M.op X0 X0) X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1025 (τ (M.op (M.op X0 X0) X0)) (τ X0) x
       have i₂ := eq29975 X0
       grind)
    | exact superpose eq29975 eq1025
    | exact resolve eq1025 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30886 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op (M.op X0 X0) X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3225 X1 (τ (M.op (M.op X0 X0) X0)) X2 (τ X0)
       have i₂ := eq29975 X0
       grind)
    | exact superpose eq29975 eq3225
    | exact resolve eq3225 eq29975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3225 eq29975
  have eq30923 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (M.op (τ X0) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq30873 X0 x
       have i₂ := eq30886 X0 (τ X0) x
       grind)
    | exact superpose eq30886 eq30873
    | exact resolve eq30873 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30873 eq30886
  have eq30977 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq30923 X0
       have i₂ := eq28387 X0
       grind)
    | exact superpose eq28387 eq30923
    | exact resolve eq30923 eq28387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28387 eq30923
  have eq31089 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq30457 (M.op (M.op x x) x)
       have i₂ := eq4153 x x x x
       grind)
    | exact superpose eq4153 eq30457
    | exact resolve eq30457 eq4153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31102 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq29847 (M.op X0 X0)
       have i₂ := eq30457 X0
       grind)
    | exact superpose eq30457 eq29847
    | (have j1 := eq30457 X0
       grind)
    | exact resolve eq29847 eq30457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29847
  have eq31106 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ X0) (τ (M.op (M.op X0 X0) X0))) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq31102 x
       have i₂ := eq1025 x x x
       grind)
    | exact superpose eq1025 eq31102
    | (have j0 := eq31102 X0
       grind)
    | exact resolve eq31102 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31102
  have eq31134 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq31106 X0
       have i₂ := eq30977 X0
       grind)
    | exact superpose eq30977 eq31106
    | (have j0 := eq31106 X0
       grind)
    | exact resolve eq31106 eq30977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30977 eq31106
  have eq31156 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op X0 X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq30457 eq31134
    | (have j0 := eq31134 X0
       have j1 := eq30457 X0
       grind)
    | exact resolve eq31134 eq30457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30457 eq31134
  have eq44410 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (τ (M.op X0 (M.op (M.op X0 X0) X0))) ∨ (M.op (M.op X0 X0) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq31156 (M.op (M.op x x) x)
       have i₂ := eq4153 x x x x
       grind)
    | exact superpose eq4153 eq31156
    | exact resolve eq31156 eq4153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31156
  have eq44509 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq44410 X0
       have i₂ := eq562 X0 X0 X0
       grind)
    | exact superpose eq562 eq44410
    | (have j0 := eq44410 X0
       grind)
    | exact resolve eq44410 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44410
  have eq44572 : ∀ X0 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X0) ≠ X0 := by
    intro X0
    first
    | exact superpose eq31089 eq44509
    | (have j0 := eq44509 X0
       have j1 := eq31089 X0
       grind)
    | exact resolve eq44509 eq31089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31089 eq44509
  have eq46158 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq25446 X0
       have i₂ := eq44572 X0
       grind)
    | exact superpose eq44572 eq25446
    | (have j0 := eq25446 X0
       have j1 := eq44572 X0
       grind)
    | exact resolve eq25446 eq44572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25446 eq44572
  have eq46185 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq46158 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46158
  have eq49931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq29629
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq29629
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq29629 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29629
  have eq49932 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq49931
  have eq206065 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) (M.op X5 X6)) X5) X1) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq1388 X0 (M.op (M.op X1 X2) X3) X4 X1 X2
       have i₂ := eq164 (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) (M.op X1 X2) X3 X5 X6
       grind)
    | (have i₁ := eq1388 X0 (M.op (M.op X1 X2) X3) X4 X1 X2
       have i₂ := eq164 (M.op X0 (M.op (M.op (M.op X1 X2) X3) X4)) X5 X6 (M.op X1 X2) X3
       grind)
    | exact superpose eq164 eq1388
    | exact resolve eq1388 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq1388
  have eq207771 : ∀ X0 X1 X5 X6 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X5 X6)) X5) X1) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq206065 X0 X1 x x x X5 X6
       have i₂ := eq8088 X0 X1 x x x
       grind)
    | exact superpose eq8088 eq206065
    | exact resolve eq206065 eq8088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8088 eq206065
  have eq209904 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (M.op X0 X0) X0) X1) (M.op X2 X3)) X2) X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4153 X0 X0 X0 X0
       have i₂ := eq207771 (M.op (M.op X0 X0) X0) X1 X2 X3
       grind)
    | exact superpose eq207771 eq4153
    | exact resolve eq4153 eq207771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4153
  have eq482521 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq49932
       grind)
    | exact superpose eq49932 eq10
    | exact resolve eq10 eq49932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49932
  have eq482718 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq482521
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq482521
    | exact resolve eq482521 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482521
  have eq482719 : (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq482718
  have eq482855 : (M.op y y) = (τ (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq482719
       grind)
    | exact superpose eq482719 eq10
    | exact resolve eq10 eq482719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482719
  have eq483052 : x = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq482855
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq482855
    | exact resolve eq482855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482855
  have eq483053 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq483052
  have eq483135 : x = (M.op (M.op y x) x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72 x
       have i₂ := eq483053
       grind)
    | exact superpose eq483053 eq72
    | exact resolve eq72 eq483053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq483246 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30068 x
       have i₂ := eq483053
       grind)
    | exact superpose eq483053 eq30068
    | exact resolve eq30068 eq483053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30068
  have eq483343 : x ≠ (M.op y x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46185 x
       have i₂ := eq483053
       grind)
    | exact superpose eq483053 eq46185
    | exact resolve eq46185 eq483053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46185
  have eq483373 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op (M.op (M.op y x) X0) (M.op X1 X2)) X1) X0) ∨ x = (M.op y y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq209904 x X0 X1 X2
       have i₂ := eq483053
       grind)
    | exact superpose eq483053 eq209904
    | exact resolve eq209904 eq483053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209904
  have eq483395 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq643 x x
       have i₂ := eq483053
       grind)
    | exact superpose eq483053 eq643
    | exact resolve eq643 eq483053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq483671 : x = (M.op (M.op y x) (M.op y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq483373 x x x
       have i₂ := eq207771 (M.op y x) x x x
       grind)
    | exact superpose eq207771 eq483373
    | exact resolve eq483373 eq207771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207771 eq483373
  have eq483728 : x = (M.op (M.op y x) y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq483671
       have i₂ := eq1025 y x x
       grind)
    | exact superpose eq1025 eq483671
    | exact resolve eq483671 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483671
  have eq483905 : ∀ X0 X1 : G, x = (M.op y (M.op (M.op y X0) X1)) ∨ x ≠ (M.op x x) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq28111 x y X0 X1
       have i₂ := eq483395
       grind)
    | exact superpose eq483395 eq28111
    | (have j0 := eq28111 x X1 x x
       grind)
    | exact resolve eq28111 eq483395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484088 : x = (M.op y y) ∨ x ≠ (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq483905 x x
       have i₂ := eq562 y x x
       grind)
    | exact superpose eq562 eq483905
    | exact resolve eq483905 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483905
  have eq484089 : x = (M.op y y) ∨ x ≠ (M.op x x) := by grind
  clear eq484088
  have eq491716 : ∀ X0 X1 : G, (M.op y x) = (M.op x (M.op (M.op x X0) X1)) ∨ (M.op y x) ≠ (M.op (M.op y x) (M.op y x)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq28111 (M.op y x) x X0 X1
       have i₂ := eq483135
       grind)
    | exact superpose eq483135 eq28111
    | (have j0 := eq28111 (M.op y x) X1 x x
       grind)
    | exact resolve eq28111 eq483135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28111 eq483135
  have eq491923 : (M.op x x) = (M.op y x) ∨ (M.op y x) ≠ (M.op (M.op y x) (M.op y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq491716 x x
       have i₂ := eq562 x x x
       grind)
    | exact superpose eq562 eq491716
    | exact resolve eq491716 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562 eq491716
  have eq492032 : (M.op y x) ≠ (M.op (M.op y x) y) ∨ (M.op x x) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq491923
       have i₂ := eq1025 y x x
       grind)
    | exact superpose eq1025 eq491923
    | exact resolve eq491923 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq491923
  have eq492086 : (M.op y x) ≠ (M.op (M.op y x) y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq483053 eq492032
    | exact resolve eq492032 eq483053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483053 eq492032
  have eq492116 : x ≠ (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq483728 eq492086
    | exact resolve eq492086 eq483728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483728 eq492086
  have eq492136 : x ≠ (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq483343 eq492116
    | exact resolve eq492116 eq483343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483343 eq492116
  have eq492141 : x = (M.op y y) ∨ x ≠ (M.op y x) := by
    first
    | (have r₁ := eq492136
       have r₂ := eq484089
       grind)
    | exact resolve eq492136 eq484089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484089 eq492136
  have eq492268 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x ≠ (M.op y x) := by
    first
    | (have i₁ := eq30160 y
       have i₂ := eq492141
       grind)
    | exact superpose eq492141 eq30160
    | exact resolve eq30160 eq492141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30160 eq492141
  have eq492719 : x ≠ (M.op y x) := by
    first
    | (have r₁ := eq492268
       have r₂ := eq16
       grind)
    | exact resolve eq492268 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492268
  have eq529236 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq483246
       grind)
    | exact superpose eq483246 eq16
    | exact resolve eq16 eq483246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483246
  have eq529631 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq483395 eq529236
    | exact resolve eq529236 eq483395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483395 eq529236
  have eq529632 : x = (M.op y y) := by grind
  clear eq529631
  have eq530290 : x = (M.op y x) := by
    first
    | (have i₁ := eq643 y y
       have i₂ := eq529632
       grind)
    | exact superpose eq529632 eq643
    | exact resolve eq643 eq529632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643 eq529632
  have eq536174 : False := by grind
  exact eq536174

/-- `Equation2656`: `x = ((x ◇ x) ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_y_pyy_pxy_Equation2656 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2656 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2656.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) = X0 := by
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
  have eq47 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op x y)) x) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X0 X0) (M.op X2 X3)) X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X0 X1
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  clear eq45
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq66
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq71
    | exact resolve eq71 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq90 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq371 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) X0) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op X0 X1)
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq48
    | exact resolve eq48 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq375 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq405 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X2 X2) X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X2 X1 (M.op (M.op X0 X0) (M.op x x)) x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X1 X1) X0) (M.op (M.op X0 X0) (M.op x x))
       have i₂ := eq49 X0 X1 x x
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq632 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq637 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq645 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq637 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq637 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq637 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq637 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq655 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq1610 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X1) (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq405 X2 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq405
    | exact resolve eq405 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1661 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq47 (M.op (M.op X0 X0) X0)
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq47
    | exact resolve eq47 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48 (M.op (M.op X0 X0) X0)
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq48
    | exact resolve eq48 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1672 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq427 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq405 X0 X0 X0
       grind)
    | exact superpose eq405 eq427
    | exact resolve eq427 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1876 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq1661 X0
       grind)
    | exact superpose eq1661 eq371
    | exact resolve eq371 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1905 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x x) x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1661 eq372
    | exact resolve eq372 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq372 eq1905
    | exact resolve eq1905 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1953 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq47 eq1876
    | exact resolve eq1876 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq2094 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq1662 X0
       grind)
    | exact superpose eq1662 eq371
    | exact resolve eq371 eq1662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2120 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq1662 eq372
    | exact resolve eq372 eq1662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1662
  have eq2132 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq372 eq2120
    | exact resolve eq2120 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq2120
  have eq2503 : (σ x) = (M.op (M.op (M.op (σ x) (σ x)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq1672
    | (have j0 := eq1672 (σ x) (σ y)
       grind)
    | exact resolve eq1672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq2527 : (σ x) = (M.op (M.op (M.op (σ x) (M.op x y)) x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2503
       have i₂ := eq1661 sF2
       grind)
    | exact superpose eq1661 eq2503
    | exact resolve eq2503 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq2503
  have eq7706 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq93 eq12
    | (have j0 := eq12 (σ y) (σ X0)
       have j1 := eq93 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ X0)
       have r₂ := eq93 X0
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq93 y
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq7729 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7706 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7706
  have eq7734 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) ∨ (k (σ y) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq7729 X0
       have j1 := eq12 (σ y) (σ X0)
       grind)
    | (have r₁ := eq7729 y
       have r₂ := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq7729 X0
       have r₂ := eq12 (σ y) (σ X0)
       grind)
    | exact resolve eq7729 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7729
  have eq7753 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq7734
    | (have j0 := eq7734 X0
       grind)
    | exact resolve eq7734 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7734
  have eq9714 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq9838 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq9714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9714
  have eq17309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq73 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq17310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17309
    | exact resolve eq17309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17309
  have eq17321 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17310
       have r₂ := eq28
       grind)
    | exact resolve eq17310 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17310
  have eq17323 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17321
    | exact resolve eq17321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17321
  have eq17326 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq17323
  have eq17422 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17326 eq58
    | exact resolve eq58 eq17326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq17326
  have eq17447 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq17422
    | exact resolve eq17422 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17422
  have eq19987 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq17447
       grind)
    | exact superpose eq17447 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17447
  have eq19988 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19987
  have eq19992 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19988
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19988
    | exact resolve eq19988 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19988
  have eq19993 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19992
  have eq20152 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq20194 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq375 y y
       have i₂ := eq19993
       grind)
    | exact superpose eq19993 eq375
    | exact resolve eq375 eq19993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19993
  have eq20226 : x = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20194
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20194
    | exact resolve eq20194 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20194
  have eq20264 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq634 x y
       have i₂ := eq20152
       grind)
    | exact superpose eq20152 eq634
    | (have j0 := eq634 x y
       grind)
    | exact resolve eq634 eq20152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq20152
  have eq20267 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20264
  have eq20270 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20267
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20267
    | exact resolve eq20267 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20267
  have eq20281 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20270
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20270
    | exact resolve eq20270 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20270
  have eq20285 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq20281
    | exact resolve eq20281 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20281
  have eq20286 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20285
  have eq20290 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20286
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20286
    | exact resolve eq20286 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20286
  have eq20293 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20290
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20290
    | exact resolve eq20290 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20290
  have eq20434 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20226 eq655
    | (have j0 := eq655 x x
       grind)
    | exact resolve eq655 eq20226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20226
  have eq20439 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20434
  have eq20442 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20439
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20439
    | exact resolve eq20439 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20439
  have eq20453 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20442
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20442
    | exact resolve eq20442 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20442
  have eq20457 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq20453
    | exact resolve eq20453 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20453
  have eq20649 : (σ y) = (M.op (M.op (σ x) (M.op x y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20293 eq47
    | exact resolve eq47 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq20684 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20293 eq50
    | exact resolve eq50 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20293
  have eq20723 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq20684
    | exact resolve eq20684 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20684
  have eq23158 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20649 eq2527
    | exact resolve eq2527 eq20649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527 eq20649
  have eq23334 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq23158 eq2094
    | exact resolve eq2094 eq23158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094 eq23158
  have eq149129 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20457 eq23334
    | exact resolve eq23334 eq20457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20457 eq23334
  have eq149331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq149129
  have eq149374 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq149331
    | exact resolve eq149331 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149331
  have eq149375 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq149374
  have eq150220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq149375 eq20723
    | exact resolve eq20723 eq149375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20723 eq149375
  have eq150434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq150220
  have eq150459 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq150434
       have r₂ := eq28
       grind)
    | exact resolve eq150434 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150434
  have eq150943 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150459 eq28
    | exact resolve eq28 eq150459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150944 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ y)) (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq150459 eq48
    | exact resolve eq48 eq150459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq150984 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150459 eq2132
    | exact resolve eq2132 eq150459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq150996 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq150984
    | exact resolve eq150984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150984
  have eq151030 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  have eq151270 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150459 eq151030
    | exact resolve eq151030 eq150459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151030
  have eq151283 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq151270
  have eq151288 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151283 eq100
    | exact resolve eq100 eq151283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq151333 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq151288
    | exact resolve eq151288 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151288
  have eq151358 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq151333
       grind)
    | exact superpose eq151333 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq151333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151333
  have eq151359 : y = (M.op x x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq151358
  have eq158424 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150996 eq150944
    | exact resolve eq150944 eq150996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150944 eq150996
  have eq158532 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq158424
  have eq158636 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150459 eq158532
    | exact resolve eq158532 eq150459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150459 eq158532
  have eq158731 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq158636
  have eq159305 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq158731 eq405
    | exact resolve eq405 eq158731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq158731
  have eq159431 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq159305 x
       have i₂ := eq427 sF2 x
       grind)
    | exact superpose eq427 eq159305
    | exact resolve eq159305 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159305
  have eq262850 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1953 x
       have i₂ := eq151359
       grind)
    | exact superpose eq151359 eq1953
    | exact resolve eq1953 eq151359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151359
  have eq263091 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq262850
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq262850
    | exact resolve eq262850 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262850
  have eq263092 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq263091
  have eq263150 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50 y x
       have i₂ := eq263092
       grind)
    | exact superpose eq263092 eq50
    | exact resolve eq50 eq263092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263157 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq375 y x
       have i₂ := eq263092
       grind)
    | exact superpose eq263092 eq375
    | exact resolve eq375 eq263092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq263178 : ∀ X0 : G, (M.op (M.op y y) y) = (M.op x (M.op (M.op x x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1610 y x X0
       have i₂ := eq263092
       grind)
    | exact superpose eq263092 eq1610
    | exact resolve eq1610 eq263092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610 eq263092
  have eq263315 : (M.op x x) = (M.op (M.op y y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263178 x
       have i₂ := eq427 x x
       grind)
    | exact superpose eq427 eq263178
    | exact resolve eq263178 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq263178
  have eq263329 : x = (k (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263157
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq263157
    | exact resolve eq263157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263157
  have eq263333 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263150
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq263150
    | exact resolve eq263150 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263150
  have eq263682 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq263329 eq655
    | (have j0 := eq655 x x
       grind)
    | exact resolve eq655 eq263329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq263329
  have eq263687 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq263682
  have eq263691 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263687
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263687
    | exact resolve eq263687 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263687
  have eq263712 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq263691
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq263691
    | exact resolve eq263691 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263691
  have eq263718 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq263712
    | exact resolve eq263712 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263712
  have eq263731 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq263333
       grind)
    | exact superpose eq263333 eq70
    | exact resolve eq70 eq263333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263333
  have eq264091 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq263731
    | exact resolve eq263731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263731
  have eq283020 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq371 y
       have i₂ := eq263315
       grind)
    | exact superpose eq263315 eq371
    | exact resolve eq371 eq263315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq263315
  have eq500288 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq159431 eq263718
    | exact resolve eq263718 eq159431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159431 eq263718
  have eq500694 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq500288
  have eq500758 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq500694
       have r₂ := eq150943
       grind)
    | exact resolve eq500694 eq150943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500694
  have eq500785 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq500758 eq30
    | exact resolve eq30 eq500758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq501070 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq500758 eq150943
    | exact resolve eq150943 eq500758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150943
  have eq501082 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq500758 eq151283
    | exact resolve eq151283 eq500758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151283 eq500758
  have eq501487 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq501082
  have eq501499 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by grind
  clear eq501070
  have eq501848 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq500785
    | exact resolve eq500785 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500785
  have eq502963 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq501848 eq1917
    | exact resolve eq1917 eq501848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501848
  have eq503243 : (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq502963
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq502963
    | exact resolve eq502963 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502963
  have eq505115 : (τ (σ x)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq501487 eq54
    | exact resolve eq54 eq501487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq505128 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq501487 eq264091
    | exact resolve eq264091 eq501487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264091 eq501487
  have eq505191 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq505128
  have eq505208 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq505191
       have r₂ := eq501499
       grind)
    | exact resolve eq505191 eq501499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501499 eq505191
  have eq505215 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq505115
    | exact resolve eq505115 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq505115
  have eq505524 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq505208
  have eq509302 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq70
       have i₂ := eq503243
       grind)
    | exact superpose eq503243 eq70
    | exact resolve eq70 eq503243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq503243
  have eq509802 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq509302
       have r₂ := eq505524
       grind)
    | exact resolve eq509302 eq505524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505524 eq509302
  have eq509831 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq509802
    | exact resolve eq509802 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509802
  have eq510541 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq505215
       grind)
    | exact superpose eq505215 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq505215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505215
  have eq510542 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq510541
  have eq517029 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq509831 eq54
    | exact resolve eq54 eq509831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq509831
  have eq517114 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq517029
    | exact resolve eq517029 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq517029
  have eq517165 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq283020
       have i₂ := eq510542
       grind)
    | exact superpose eq510542 eq283020
    | exact resolve eq283020 eq510542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283020 eq510542
  have eq517560 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq517165
  have eq517681 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq517560
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq517560
    | exact resolve eq517560 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517560
  have eq517682 : y = (M.op x y) := by grind
  clear eq517681
  have eq517701 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq517682 eq21
    | exact resolve eq21 eq517682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq517810 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq517682 eq1917
    | exact resolve eq1917 eq517682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq518096 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq517810
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq517810
    | exact resolve eq517810 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq517810
  have eq518163 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq517701
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq517701
    | exact resolve eq517701 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517701
  have eq518168 : y = (M.op x x) := by
    first
    | exact superpose eq517682 eq518096
    | exact resolve eq518096 eq517682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518096
  have eq518177 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq518163 eq27
    | exact resolve eq27 eq518163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq518856 : x = (k y x) := by grind
  have eq518952 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq9838 x
       have i₂ := eq518168
       grind)
    | exact superpose eq518168 eq9838
    | exact resolve eq9838 eq518168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9838 eq518168
  have eq519303 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq518952
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq518952
    | exact resolve eq518952 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518952
  have eq519411 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq519303
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq519303
    | exact resolve eq519303 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519303
  have eq519428 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq518163 eq519411
    | exact resolve eq519411 eq518163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519411
  have eq519432 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq519428
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq519428
    | exact resolve eq519428 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519428
  have eq519435 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq519432
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq519432
    | exact resolve eq519432 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519432
  have eq519437 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq518163 eq519435
    | exact resolve eq519435 eq518163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519435
  have eq519767 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7753 x
       have i₂ := eq518856
       grind)
    | exact superpose eq518856 eq7753
    | (have j0 := eq7753 x
       grind)
    | exact resolve eq7753 eq518856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7753 eq518856
  have eq519782 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq519767
  have eq519791 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq519782
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq519782
    | exact resolve eq519782 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519782
  have eq519812 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq519791
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq519791
    | exact resolve eq519791 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519791
  have eq519833 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq518163 eq519812
    | exact resolve eq519812 eq518163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519812
  have eq535175 : y = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq517682 eq517114
    | exact resolve eq517114 eq517682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517114
  have eq535176 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq517682 eq535175
    | exact resolve eq535175 eq517682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517682 eq535175
  have eq535181 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq535176
       grind)
    | exact superpose eq535176 eq44
    | exact resolve eq44 eq535176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq535176
  have eq535322 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq535181
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq535181
    | exact resolve eq535181 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535181
  have eq535380 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq518163 eq535322
    | exact resolve eq535322 eq518163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535322
  have eq677326 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq519437 eq50
    | exact resolve eq50 eq519437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq519437
  have eq677686 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq518177 eq677326
    | exact resolve eq677326 eq518177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677326
  have eq679672 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  have eq680042 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  have eq680359 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq677686 eq519833
    | exact resolve eq519833 eq677686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519833 eq677686
  have eq680951 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq680359
       have r₂ := eq28
       grind)
    | exact resolve eq680359 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680359
  have eq683040 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq680951 eq1953
    | exact resolve eq1953 eq680951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680951
  have eq683523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq518177 eq683040
    | exact resolve eq683040 eq518177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683040
  have eq683598 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq683523
       have r₂ := eq28
       grind)
    | exact resolve eq683523 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683523
  have eq683631 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq683598 eq28
    | exact resolve eq28 eq683598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683598
  have eq695086 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq679672 eq535380
    | exact resolve eq535380 eq679672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535380 eq679672
  have eq695205 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq695086
       have r₂ := eq680042
       grind)
    | exact resolve eq695086 eq680042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680042 eq695086
  have eq695367 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq695205 eq1953
    | exact resolve eq1953 eq695205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953 eq695205
  have eq695875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq518177 eq695367
    | exact resolve eq695367 eq518177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518177 eq695367
  have eq695976 : x = y := by
    first
    | (have r₁ := eq695875
       have r₂ := eq28
       grind)
    | exact resolve eq695875 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq695875
  have eq696028 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq695976
       grind)
    | exact superpose eq695976 eq25
    | exact resolve eq25 eq695976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq695976
  have eq697079 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq518163 eq696028
    | exact resolve eq696028 eq518163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518163 eq696028
  have eq697463 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq697079
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq697079
    | exact resolve eq697079 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq697079
  have eq697663 : False := by grind
  exact eq697663

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_x_pyx_x_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
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
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq17
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq18
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq90 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq182 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq90
    | exact resolve eq90 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq341 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq182
    | exact resolve eq182 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq590 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq590 X0
       grind)
    | exact superpose eq590 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq590 X1
       grind)
    | exact superpose eq590 eq593
    | (have j0 := eq593 X0 X1
       grind)
    | (have r₁ := eq593 X0 X0
       have r₂ := eq590 X0
       grind)
    | exact resolve eq593 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq692 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq341 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq341
    | exact resolve eq341 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq1360 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq692
    | exact resolve eq692 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq2206 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2211 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2213 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2211 X0 X1
       have i₂ := eq590 X1
       grind)
    | exact superpose eq590 eq2211
    | (have j0 := eq2211 X0 X1
       grind)
    | exact resolve eq2211 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2217 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2206
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq2206
    | exact resolve eq2206 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2219 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2213 X0 X1
       have i₂ := eq590 X0
       grind)
    | exact superpose eq590 eq2213
    | (have j0 := eq2213 X0 X1
       grind)
    | exact resolve eq2213 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2223 : (M.op x x) = (k y y) ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2217
       have i₂ := eq590 y
       grind)
    | exact superpose eq590 eq2217
    | exact resolve eq2217 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2228 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2223
       have i₂ := eq590 x
       grind)
    | exact superpose eq590 eq2223
    | exact resolve eq2223 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2235 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (k y y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2228
       have i₂ := eq11 (σ x) (σ y)
       grind)
    | exact superpose eq11 eq2228
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq2228
       have r₂ := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq2228 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq2236 : (k y y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq2235
  have eq2237 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k y y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2236
       have i₂ := eq590 (σ y)
       grind)
    | exact superpose eq590 eq2236
    | exact resolve eq2236 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq2238 : (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2237
       have i₂ := eq590 (σ x)
       grind)
    | exact superpose eq590 eq2237
    | exact resolve eq2237 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237
  have eq2310 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2238
       grind)
    | exact superpose eq2238 eq10
    | exact resolve eq10 eq2238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq2311 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2310
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2310
    | exact resolve eq2310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2312 : x = (M.op x y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2311
  have eq2387 : x ≠ x ∨ (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2312
       grind)
    | exact superpose eq2312 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2312
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2312
       grind)
    | exact resolve eq12 eq2312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq2389 : (M.op x x) = (M.op y y) ∨ x = (k x y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2387
  have eq2391 : (M.op x x) = (k y y) ∨ x = (k x y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2389
       have i₂ := eq590 y
       grind)
    | exact superpose eq590 eq2389
    | exact resolve eq2389 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2393 : x = (k x y) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2391
       have i₂ := eq590 x
       grind)
    | exact superpose eq590 eq2391
    | exact resolve eq2391 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2552 : (k y y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 x y
       have i₂ := eq2393
       grind)
    | exact superpose eq2393 eq10
    | exact resolve eq10 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq2632 : x ≠ (k x y) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq2219 x y
       grind)
    | exact superpose eq2219 eq9
    | (have j1 := eq2219 x y
       grind)
    | exact resolve eq9 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2721 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1360 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1360
    | exact resolve eq1360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq2792 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2552
       grind)
    | exact superpose eq2552 eq10
    | exact resolve eq10 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2793 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2792
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2792
    | exact resolve eq2792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2792
  have eq2794 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq2793
  have eq2869 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq2794
       grind)
    | exact superpose eq2794 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2794
       grind)
    | exact resolve eq12 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2794
  have eq2871 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq2869
  have eq2872 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq2871
  have eq2875 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2872
       have i₂ := eq590 (σ y)
       grind)
    | exact superpose eq590 eq2872
    | exact resolve eq2872 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2877 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2875
       have i₂ := eq590 (σ x)
       grind)
    | exact superpose eq590 eq2875
    | exact resolve eq2875 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq2875
  have eq2878 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2877
  have eq2881 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq2878
       grind)
    | exact superpose eq2878 eq17
    | exact resolve eq17 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2946 : (k y y) = (k x x) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2881
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq2881
    | exact resolve eq2881 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2881
  have eq6801 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2721 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq2721
    | exact resolve eq2721 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721
  have eq13545 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6801 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6801
    | exact resolve eq6801 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq28261 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq597 y x
       grind)
    | exact superpose eq597 eq9
    | (have j1 := eq597 y x
       grind)
    | exact resolve eq9 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28315 : (k y y) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq28261
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq28261
    | exact resolve eq28261 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28261
  have eq28458 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq28315
       have i₂ := eq2946
       grind)
    | exact superpose eq2946 eq28315
    | (have r₁ := eq28315
       have r₂ := eq2946
       grind)
    | exact resolve eq28315 eq2946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq28463 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq28458
  have eq28472 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28463
       have i₂ := eq597 (σ y) (σ x)
       grind)
    | exact superpose eq597 eq28463
    | (have j1 := eq597 (σ y) (σ x)
       grind)
    | (have r₁ := eq28463
       have r₂ := eq597 (σ y) (σ x)
       grind)
    | exact resolve eq28463 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28463
  have eq28476 : (σ x) = (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq28472
  have eq28479 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq28476
       have r₂ := eq2878
       grind)
    | exact resolve eq28476 eq2878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878 eq28476
  have eq28575 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | (have i₁ := eq13545 y (σ x)
       have i₂ := eq28479
       grind)
    | exact superpose eq28479 eq13545
    | exact resolve eq13545 eq28479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13545
  have eq28578 : x = (k x y) := by
    first
    | (have i₁ := eq28575
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq28575
    | exact resolve eq28575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28575
  have eq28675 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k y y) = (k x x) := by
    first
    | (have r₁ := eq2632
       have r₂ := eq28578
       grind)
    | exact resolve eq2632 eq28578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632 eq28578
  have eq28740 : (σ x) ≠ (σ x) ∨ (k y y) = (k x x) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28675
       have i₂ := eq2219 (σ x) (σ y)
       grind)
    | exact superpose eq2219 eq28675
    | (have j1 := eq2219 (σ x) (σ y)
       grind)
    | (have r₁ := eq28675
       have r₂ := eq2219 (σ x) (σ y)
       grind)
    | exact resolve eq28675 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219 eq28675
  have eq28742 : (k y y) = (k x x) ∨ (σ x) ≠ (k (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq28740
  have eq28751 : (σ x) ≠ (σ x) ∨ (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28742
       have i₂ := eq28479
       grind)
    | exact superpose eq28479 eq28742
    | (have r₁ := eq28742
       have r₂ := eq28479
       grind)
    | exact resolve eq28742 eq28479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28479 eq28742
  have eq28752 : (k y y) = (k x x) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq28751
  have eq29498 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq28752
       grind)
    | exact superpose eq28752 eq10
    | exact resolve eq10 eq28752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28752
  have eq29506 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq29498
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq29498
    | exact resolve eq29498 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29498
  have eq29507 : (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq29506
  have eq32161 : (k y y) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq29507
       grind)
    | exact superpose eq29507 eq17
    | exact resolve eq17 eq29507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32357 : (k y y) = (k x x) := by
    first
    | (have i₁ := eq32161
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq32161
    | exact resolve eq32161 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq32161
  have eq32452 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq28315
       have r₂ := eq32357
       grind)
    | exact resolve eq28315 eq32357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28315 eq32357
  have eq33332 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq32452
       have i₂ := eq597 (σ y) (σ x)
       grind)
    | exact superpose eq597 eq32452
    | (have j1 := eq597 (σ y) (σ x)
       grind)
    | (have r₁ := eq32452
       have r₂ := eq597 (σ y) (σ x)
       grind)
    | exact resolve eq32452 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq32452
  have eq33336 : (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq33332
  have eq33341 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq33336
       have i₂ := eq29507
       grind)
    | exact superpose eq29507 eq33336
    | (have r₁ := eq33336
       have r₂ := eq29507
       grind)
    | exact resolve eq33336 eq29507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29507 eq33336
  have eq33342 : False := by grind
  exact eq33342

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pyy_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq42 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq48
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq43 X1 X0
       grind)
    | (have r₁ := eq53 X1 X0
       have r₂ := eq43 X0 X1
       grind)
    | (have r₁ := eq53 X0 X0
       have r₂ := eq43 X0 X0
       grind)
    | exact resolve eq53 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq53
  have eq145 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq152 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq145 X0 X0
       have r₂ := eq55 X0 X0
       grind)
    | exact resolve eq145 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq145
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq152 (σ X0) (σ X1)
       grind)
    | exact superpose eq152 eq15
    | exact resolve eq15 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq295 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq288 X0 X1
       have i₂ := eq152 X0 X1
       grind)
    | exact superpose eq152 eq288
    | exact resolve eq288 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq288
  have eq297 : False := by grind
  exact eq297

/-- `Equation2659`: `x = ((x ◇ y) ◇ (x ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pxy_Equation2659 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2659 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2659.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq141 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq146 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq151 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq400 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq152 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq152
    | exact resolve eq152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152 x y
       grind)
    | exact superpose eq152 eq16
    | (have j1 := eq152 x y
       grind)
    | exact resolve eq16 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq425 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq400
    | (have j0 := eq400 X0 X1
       grind)
    | exact resolve eq400 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq400
  have eq432 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq425
    | exact resolve eq425 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq569 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq407
       have i₂ := eq432 x y
       grind)
    | exact superpose eq432 eq407
    | (have j1 := eq432 (σ x) (σ y)
       grind)
    | (have r₁ := eq407
       have r₂ := eq432 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq407
       have r₂ := eq432 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq407 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407 eq432
  have eq572 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq569
  have eq574 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq572
       grind)
    | exact superpose eq572 eq10
    | exact resolve eq10 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq608 : x = y ∨ x = y := by
    first
    | (have i₁ := eq574
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq574
    | exact resolve eq574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq609 : x = y := by grind
  clear eq608
  have eq644 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq609
       grind)
    | exact superpose eq609 eq16
    | exact resolve eq16 eq609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq645 : False := by grind
  exact eq645
