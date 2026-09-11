import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation3499 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3499 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
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
  clear eq36
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
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq176 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X3) = (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 X4 X2
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq16 X0 (M.op x x) X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq179 X0 x X2
       have i₂ := eq16 X0 (M.op (M.op x x) X0) x
       grind)
    | (have i₁ := eq179 X0 x X2
       have i₂ := eq16 (M.op (M.op x x) X0) x X2
       grind)
    | exact superpose eq16 eq179
    | exact resolve eq179 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq188 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq548 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X3) = (k (M.op X0 (M.op (M.op X1 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq192
    | exact resolve eq192 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (k (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq16
    | exact resolve eq16 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X1 (M.op X0 X0)
       have i₂ := eq192 X0 (M.op X1 X1)
       grind)
    | exact superpose eq192 eq181
    | exact resolve eq181 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (k (M.op X1 X1) X2)) X3) = (k (M.op X0 (k (M.op X1 X1) X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq548 X0 X0 X1 X3
       have i₂ := eq192 X0 X1
       grind)
    | exact superpose eq192 eq548
    | exact resolve eq548 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1082 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact superpose eq181 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1085 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1082 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1099 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq1114 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1116 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1117 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1127 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1099 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1136 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1127 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1127 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1127 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1146 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1117 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1117
    | (have j0 := eq1117 (σ X0)
       grind)
    | exact resolve eq1117 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1150 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1136 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1136
    | (have j0 := eq1136 (σ X0) X1
       grind)
    | exact resolve eq1136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : ∀ X0 : G, (τ (σ y)) = (k y (τ (M.op X0 X0))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq107 (M.op X0 X0)
       have i₂ := eq1085 X0 sF3
       grind)
    | exact superpose eq1085 eq107
    | (have j1 := eq1085 X0 (σ y)
       grind)
    | exact resolve eq107 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1085
  have eq1178 : ∀ X0 : G, y = (k y (τ (M.op X0 X0))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq31 eq1173
    | exact resolve eq1173 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq2375 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 X2 X3 X4 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq176
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2493 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq2375 X0 X1 X2 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2576 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (M.op (M.op X2 (k (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2493 X0 X1 X2 X3 X4
       have i₂ := eq192 X3 X4
       grind)
    | exact superpose eq192 eq2493
    | (have j0 := eq2493 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2493 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq2640 : ∀ X0 X1 X2 X3 X4 : G, (k X0 X0) = (M.op X1 (k (M.op X2 (k (M.op X3 X3) X4)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2576 X0 X1 X2 X3 X4
       have i₂ := eq569 X2 X3 X4 X0
       grind)
    | exact superpose eq569 eq2576
    | (have j0 := eq2576 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq2576 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq2576
  have eq8056 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1113
       grind)
    | exact superpose eq1113 eq39
    | exact resolve eq39 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq8056
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8056
    | exact resolve eq8056 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8056
  have eq8061 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq8057
    | exact resolve eq8057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8057
  have eq16896 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1146 (M.op X0 X0)
       have i₂ := eq561 X0 X0
       grind)
    | exact superpose eq561 eq1146
    | (have j0 := eq1146 (M.op X0 X0)
       grind)
    | exact resolve eq1146 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq1146
  have eq16932 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq16896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16896
  have eq17086 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq181 (σ (M.op X0 X0)) x
       have i₂ := eq16932 X0
       grind)
    | exact superpose eq16932 eq181
    | exact resolve eq181 eq16932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16932
  have eq17798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8061 eq1114
    | exact resolve eq1114 eq8061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17807 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq17798
       have r₂ := eq27
       grind)
    | exact resolve eq17798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17798
  have eq17823 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17807 eq181
    | exact resolve eq181 eq17807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17826 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17807 eq192
    | exact resolve eq192 eq17807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17807
  have eq19016 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17823 eq26
    | (have j1 := eq17823 (σ x)
       grind)
    | exact resolve eq26 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19086 : y = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19016 eq1178
    | exact resolve eq1178 eq19016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq19016
  have eq19113 : y = (k y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq19086
    | exact resolve eq19086 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19086
  have eq19125 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq19113
       have r₂ := eq12 x (σ y)
       grind)
    | (have r₁ := eq19113
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq19113
       have r₂ := eq12 x y
       grind)
    | exact resolve eq19113 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19113
  have eq19235 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19125 eq181
    | exact resolve eq181 eq19125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19125
  have eq19334 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19235 eq26
    | (have j1 := eq19235 (σ x)
       grind)
    | exact resolve eq26 eq19235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19235
  have eq19336 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq19334
  have eq19344 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1113
       have i₂ := eq19336
       grind)
    | exact superpose eq19336 eq1113
    | exact resolve eq1113 eq19336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq19348 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq19336
       grind)
    | exact superpose eq19336 eq39
    | exact resolve eq39 eq19336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19336
  have eq19349 : y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19344
  have eq19351 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19348
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19348
    | exact resolve eq19348 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19348
  have eq19358 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19351 eq8061
    | exact resolve eq8061 eq19351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8061
  have eq19360 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq19351 eq1114
    | exact resolve eq1114 eq19351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1114 eq19351
  have eq19365 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq19360
  have eq19366 : y = (M.op y y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19358
  have eq20153 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 y x
       have i₂ := eq19349
       grind)
    | exact superpose eq19349 eq181
    | exact resolve eq181 eq19349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19349
  have eq20249 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17086 y x
       have i₂ := eq19366
       grind)
    | exact superpose eq19366 eq17086
    | exact resolve eq17086 eq19366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19366
  have eq20262 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20249 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20249
    | (have j0 := eq20249 X0
       grind)
    | exact resolve eq20249 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20249
  have eq20343 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20153 x
       grind)
    | exact superpose eq20153 eq18
    | (have j1 := eq20153 x
       grind)
    | exact resolve eq18 eq20153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20153
  have eq20346 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20343
  have eq20369 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq181 x x
       have i₂ := eq20346
       grind)
    | exact superpose eq20346 eq181
    | exact resolve eq181 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20372 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq192 x x
       have i₂ := eq20346
       grind)
    | exact superpose eq20346 eq192
    | exact resolve eq192 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20392 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq17086 x x
       have i₂ := eq20346
       grind)
    | exact superpose eq20346 eq17086
    | exact resolve eq17086 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20346
  have eq20398 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq20392 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20392
    | (have j0 := eq20392 X0
       grind)
    | exact resolve eq20392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20392
  have eq20529 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20398 eq192
    | exact resolve eq192 eq20398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20398
  have eq20632 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20372 y
       grind)
    | exact superpose eq20372 eq18
    | (have j1 := eq20372 y
       grind)
    | exact resolve eq18 eq20372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20698 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20369 x
       have i₂ := eq20372 x
       grind)
    | exact superpose eq20372 eq20369
    | exact resolve eq20369 eq20372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20369 eq20372
  have eq20709 : x = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20698
  have eq20810 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq20632
       grind)
    | exact superpose eq20632 eq40
    | exact resolve eq40 eq20632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20632
  have eq20811 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20810
    | exact resolve eq20810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20810
  have eq20815 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20811
    | exact resolve eq20811 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20811
  have eq20825 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq20709
       grind)
    | exact superpose eq20709 eq39
    | exact resolve eq39 eq20709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq20709
  have eq20837 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20825
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20825
    | exact resolve eq20825 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20825
  have eq21049 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20529 eq26
    | (have j1 := eq20529 (σ y)
       grind)
    | exact resolve eq26 eq20529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20529
  have eq21180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20815 eq21049
    | exact resolve eq21049 eq20815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20815 eq21049
  have eq21209 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21180
       have r₂ := eq27
       grind)
    | exact resolve eq21180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21180
  have eq21220 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21209 eq27
    | exact resolve eq27 eq21209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23671 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20262 eq26
    | (have j1 := eq20262 (σ x)
       grind)
    | exact resolve eq26 eq20262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20262
  have eq23676 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23671
  have eq23715 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq192 x x
       have i₂ := eq23676
       grind)
    | exact superpose eq23676 eq192
    | exact resolve eq192 eq23676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23736 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq17086 x x
       have i₂ := eq23676
       grind)
    | exact superpose eq23676 eq17086
    | exact resolve eq17086 eq23676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23676
  have eq23756 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq23736 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23736
    | (have j0 := eq23736 X0
       grind)
    | exact resolve eq23736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23736
  have eq23919 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq23756 eq192
    | exact resolve eq192 eq23756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq23756
  have eq24059 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23715 y
       grind)
    | exact superpose eq23715 eq18
    | (have j1 := eq23715 y
       grind)
    | exact resolve eq18 eq23715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23715
  have eq24236 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21209 eq24059
    | exact resolve eq24059 eq21209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24059
  have eq24590 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23919 eq26
    | (have j1 := eq23919 (σ y)
       grind)
    | exact resolve eq26 eq23919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23919
  have eq24808 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24590 eq98
    | exact resolve eq98 eq24590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq24590
  have eq24824 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21209 eq24808
    | exact resolve eq24808 eq21209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24808
  have eq24829 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24236 eq24824
    | exact resolve eq24824 eq24236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24236 eq24824
  have eq24832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq24829 eq14
    | exact resolve eq14 eq24829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24829
  have eq24883 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq24832
    | exact resolve eq24832 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24832
  have eq24885 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq24883
       have r₂ := eq27
       grind)
    | exact resolve eq24883 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24883
  have eq25682 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq555 (k (M.op x x) x) X0 x
       have i₂ := eq2640 X0 x (k (M.op x x) x) x x
       grind)
    | exact superpose eq2640 eq555
    | (have j1 := eq2640 X0 x x x x
       grind)
    | exact resolve eq555 eq2640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq25808 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25682 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq25682 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq25682 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25682
  have eq43451 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19365 eq181
    | exact resolve eq181 eq19365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19365
  have eq43585 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq43451 X0
       have i₂ := eq25808 sF2
       grind)
    | exact superpose eq25808 eq43451
    | (have j0 := eq43451 X0
       grind)
    | exact resolve eq43451 eq25808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43451
  have eq43633 : ∀ X0 : G, y = (k y y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43585 X0
       have i₂ := eq25808 y
       grind)
    | exact superpose eq25808 eq43585
    | (have j0 := eq43585 X0
       grind)
    | exact resolve eq43585 eq25808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43585
  have eq43678 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20837 eq43633
    | (have j0 := eq43633 X0
       grind)
    | exact resolve eq43633 eq20837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20837 eq43633
  have eq44929 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43678 eq26
    | (have j1 := eq43678 (σ x)
       grind)
    | exact resolve eq26 eq43678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43678
  have eq44935 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq44929
  have eq45002 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq44935 eq141
    | exact resolve eq141 eq44935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44935
  have eq45031 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq29 eq45002
    | exact resolve eq45002 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45002
  have eq45047 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) X0) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq45031 eq1136
    | (have j0 := eq1136 (M.op x y) X0
       grind)
    | (have r₁ := eq1136 (M.op x y) x
       have r₂ := eq45031
       grind)
    | (have r₁ := eq1136 x x
       have r₂ := eq45031
       grind)
    | exact resolve eq1136 eq45031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45055 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq45047 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45047
  have eq46166 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (k (M.op x y) (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq45055 eq181
    | exact resolve eq181 eq45055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq45055
  have eq46483 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq45031 eq46166
    | exact resolve eq46166 eq45031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45031 eq46166
  have eq46778 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq46483 eq17086
    | exact resolve eq17086 eq46483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17086 eq46483
  have eq46893 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq20 eq46778
    | (have j0 := eq46778 X0
       grind)
    | exact resolve eq46778 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46778
  have eq46942 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    intro X0
    first
    | exact superpose eq24885 eq46893
    | exact resolve eq46893 eq24885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46893
  have eq47156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | exact superpose eq46942 eq26
    | (have j1 := eq46942 (σ x)
       grind)
    | exact resolve eq26 eq46942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46942
  have eq47164 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq47156
  have eq47228 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1136 x X0
       have i₂ := eq47164
       grind)
    | exact superpose eq47164 eq1136
    | (have j0 := eq1136 x X0
       grind)
    | (have r₁ := eq1136 x x
       have r₂ := eq47164
       grind)
    | exact resolve eq1136 eq47164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47230 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1150 x X0
       have i₂ := eq47164
       grind)
    | exact superpose eq47164 eq1150
    | (have j0 := eq1150 x X0
       grind)
    | exact resolve eq1150 eq47164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47164
  have eq47234 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq47230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47230
  have eq47236 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq47228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47228
  have eq47247 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq47234 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47234
    | (have j0 := eq47234 X0
       grind)
    | exact resolve eq47234 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47234
  have eq47381 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq47236 y
       grind)
    | exact superpose eq47236 eq18
    | (have j1 := eq47236 y
       grind)
    | exact resolve eq18 eq47236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47236
  have eq47730 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21209 eq47381
    | exact resolve eq47381 eq21209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21209 eq47381
  have eq48224 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47730 eq35
    | exact resolve eq35 eq47730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq47730
  have eq48241 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq48224
    | exact resolve eq48224 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48224
  have eq48245 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24885 eq48241
    | exact resolve eq48241 eq24885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24885 eq48241
  have eq50867 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47247 eq26
    | (have j1 := eq47247 (σ y)
       grind)
    | exact resolve eq26 eq47247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47247
  have eq51230 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48245 eq50867
    | exact resolve eq50867 eq48245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48245 eq50867
  have eq51231 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq51230
  have eq51334 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq51231 eq27
    | exact resolve eq27 eq51231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq291948 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq17826 eq17823
    | exact resolve eq17823 eq17826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17823 eq17826
  have eq291949 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq291948
  have eq292008 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq291949
       have i₂ := eq25808 sF2
       grind)
    | exact superpose eq25808 eq291949
    | exact resolve eq291949 eq25808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291949
  have eq292209 : x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq292008
       have i₂ := eq25808 x
       grind)
    | exact superpose eq25808 eq292008
    | exact resolve eq292008 eq25808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292008
  have eq292384 : (σ y) = (k (σ y) (σ y)) ∨ x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq292209
       have i₂ := eq25808 y
       grind)
    | exact superpose eq25808 eq292209
    | exact resolve eq292209 eq25808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292209
  have eq292961 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq292384 eq152
    | exact resolve eq152 eq292384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq292384
  have eq293075 : y = (k y y) ∨ x = (k x x) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq292961
    | exact resolve eq292961 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq292961
  have eq293076 : (σ x) = (k (σ x) (σ x)) ∨ x = (k x x) ∨ y = (k y y) := by grind
  clear eq293075
  have eq293141 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq293076 eq141
    | exact resolve eq141 eq293076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq293076
  have eq293261 : x = (k x x) ∨ x = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq29 eq293141
    | exact resolve eq293141 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq293141
  have eq293262 : y = (k y y) ∨ x = (k x x) := by grind
  clear eq293261
  have eq293281 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op y X0) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq1136 y X0
       have i₂ := eq293262
       grind)
    | exact superpose eq293262 eq1136
    | (have j0 := eq1136 y X0
       grind)
    | (have r₁ := eq1136 y x
       have r₂ := eq293262
       grind)
    | (have r₁ := eq1136 x x
       have r₂ := eq293262
       grind)
    | exact resolve eq1136 eq293262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293382 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq293281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293281
  have eq293738 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (k (k y y) X0)) ∨ x = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq555 y X0 X1
       have i₂ := eq293382 y
       grind)
    | exact superpose eq293382 eq555
    | exact resolve eq555 eq293382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq293382
  have eq294362 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k (k y y) X0)) ∨ x = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq293738 X0 X1
       have i₂ := eq25808 X0
       grind)
    | exact superpose eq25808 eq293738
    | exact resolve eq293738 eq25808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25808 eq293738
  have eq294530 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k y X0)) ∨ x = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq293262 eq294362
    | exact resolve eq294362 eq293262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294362
  have eq298260 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x x) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq294530 y x
       have i₂ := eq293262
       grind)
    | exact superpose eq293262 eq294530
    | exact resolve eq294530 eq293262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293262 eq294530
  have eq299134 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k x x) := by
    intro X0
    first
    | (have j0 := eq298260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298260
  have eq300133 : x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq299134 x
       grind)
    | exact superpose eq299134 eq18
    | (have j1 := eq299134 x
       grind)
    | exact resolve eq18 eq299134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299134
  have eq304132 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1136 x X0
       have i₂ := eq300133
       grind)
    | exact superpose eq300133 eq1136
    | (have j0 := eq1136 x X0
       grind)
    | (have r₁ := eq1136 x x
       have r₂ := eq300133
       grind)
    | exact resolve eq1136 eq300133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq304134 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1150 x X0
       have i₂ := eq300133
       grind)
    | exact superpose eq300133 eq1150
    | (have j0 := eq1150 x X0
       grind)
    | exact resolve eq1150 eq300133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150 eq300133
  have eq304217 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq304134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304134
  have eq304219 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq304132 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304132
  have eq304231 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq304217 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq304217
    | (have j0 := eq304217 X0
       grind)
    | exact resolve eq304217 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304217
  have eq306083 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq304219 y
       grind)
    | exact superpose eq304219 eq18
    | (have j1 := eq304219 y
       grind)
    | exact resolve eq18 eq304219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq304219
  have eq307205 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq306083
       grind)
    | exact superpose eq306083 eq40
    | exact resolve eq40 eq306083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq306083
  have eq307214 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq307205
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq307205
    | exact resolve eq307205 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq307205
  have eq307218 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq307214
    | exact resolve eq307214 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307214
  have eq307571 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq304231 eq26
    | (have j1 := eq304231 (σ y)
       grind)
    | exact resolve eq26 eq304231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq304231
  have eq308317 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq51231 eq307571
    | exact resolve eq307571 eq51231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51231 eq307571
  have eq308726 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq308317 eq307218
    | exact resolve eq307218 eq308317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307218 eq308317
  have eq308781 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq308726
  have eq308793 : y = (M.op x y) := by
    first
    | (have r₁ := eq308781
       have r₂ := eq21220
       grind)
    | exact resolve eq308781 eq21220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21220 eq308781
  have eq308802 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq308793
       grind)
    | exact superpose eq308793 eq24
    | exact resolve eq24 eq308793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq308793
  have eq308876 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq308802 eq20
    | exact resolve eq20 eq308802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq308802
  have eq309035 : False := by grind
  exact eq309035

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 (M.op (M.op x x) x) x x
       have i₂ := eq9 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq24 X1 X0
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq24 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq24 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq98 X0
       have j1 := eq69 X0 X0 X0
       grind)
    | (have r₁ := eq98 X0
       have r₂ := eq69 X0 (k X0 X0) x
       grind)
    | (have r₁ := eq98 x
       have r₂ := eq69 x x x
       grind)
    | (have r₁ := eq98 (M.op X0 X0)
       have r₂ := eq69 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact resolve eq98 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq98
  have eq109 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq107 (σ X0)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq109
    | exact resolve eq109 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq109
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq136 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq131 X0 X1
       have i₂ := eq114 X1
       grind)
    | exact superpose eq114 eq131
    | (have j0 := eq131 X0 X1
       grind)
    | exact resolve eq131 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq166 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq24
    | exact resolve eq24 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq114
  have eq260 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ X1 ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq166 X0 X1
       grind)
    | exact superpose eq166 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (σ (M.op X0 X0))
       have r₂ := eq166 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq12 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq2244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq136 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq136 X0 X1
       grind)
    | exact superpose eq136 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq136 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq136 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq136 X0 X1
       grind)
    | exact resolve eq13 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq2254 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2244 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244
  have eq2259 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2254 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2254 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq2254 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254
  have eq2266 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2259 X0 X1
       have j1 := eq260 X0 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2259 X0 (M.op X0 X0)
       have r₂ := eq260 X0 (σ (M.op (M.op X0 X0) (M.op X0 X0))) x
       grind)
    | (have r₁ := eq2259 X0 X0
       have r₂ := eq260 X0 (σ X0) x
       grind)
    | exact resolve eq2259 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq2259
  have eq2272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2266 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2266
    | (have j0 := eq2266 X0 X1
       grind)
    | exact resolve eq2266 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2273 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2272
  have eq2284 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2273 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2273
    | exact resolve eq2273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2316 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2273 x y
       grind)
    | exact superpose eq2273 eq16
    | exact resolve eq16 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq4270 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq2284 X0 (τ X1)
       grind)
    | exact superpose eq2284 eq18
    | exact resolve eq18 eq2284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2284
  have eq4283 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4270 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4270
    | exact resolve eq4270 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq4302 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4283 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4283
    | exact resolve eq4283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4283
  have eq4395 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2316
       have i₂ := eq4302 x y
       grind)
    | exact superpose eq4302 eq2316
    | exact resolve eq2316 eq4302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316 eq4302
  have eq4396 : False := by grind
  exact eq4396

/-- `Equation3506`: `x ◇ x = y ◇ ((z ◇ w) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyy_pxy_Equation3506 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3506 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3506.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X3) X3)) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 x (M.op (M.op x x) x)
       have i₂ := eq16 X0 (M.op x (M.op (M.op x x) x)) x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 (M.op (M.op x x) x) x x
       have i₂ := eq16 (M.op (M.op x x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq181
    | exact resolve eq181 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq205 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq182 X1 X0
       grind)
    | (have i₁ := eq174 X1
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq174
    | exact resolve eq174 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq221 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X1
       have i₂ := eq205 X1 X0
       grind)
    | exact superpose eq205 eq174
    | exact resolve eq174 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (k X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq221 (σ X1) X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq221 X0 (σ X1)
       grind)
    | exact superpose eq221 eq10
    | exact resolve eq10 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (k y y) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq115
       have i₂ := eq221 sF3 x
       grind)
    | (have i₁ := eq115
       have i₂ := eq221 X0 sF3
       grind)
    | exact superpose eq221 eq115
    | exact resolve eq115 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq348 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X1 x
       have i₂ := eq249 x X0
       grind)
    | exact superpose eq249 eq249
    | exact resolve eq249 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 X3 : G, (k X3 X3) = (M.op X0 (k X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq205 x X3
       have i₂ := eq184 X1 x X0
       grind)
    | (have i₁ := eq205 (k X0 X0) X1
       have i₂ := eq184 X0 X1 (k X0 X0)
       grind)
    | exact superpose eq184 eq205
    | exact resolve eq205 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq205
  have eq937 : ∀ X0 X1 X2 : G, (k X1 X1) = (M.op X2 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq614 X2 x X1
       have i₂ := eq249 x X0
       grind)
    | exact superpose eq249 eq614
    | exact resolve eq614 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq1212 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (σ (k X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq348 x X1
       have i₂ := eq348 X0 x
       grind)
    | exact superpose eq348 eq348
    | exact resolve eq348 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : ∀ X0 X1 : G, (k X1 X1) = (σ (σ (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq249 X1 x
       have i₂ := eq348 X0 x
       grind)
    | exact superpose eq348 eq249
    | exact resolve eq249 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq348
  have eq1595 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = y := by
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
  have eq1598 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq1604 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1598
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1598
    | exact resolve eq1598 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1607 : (M.op x y) = (k x y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq1595
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1595
    | exact resolve eq1595 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq5470 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1607
       grind)
    | exact superpose eq1607 eq40
    | exact resolve eq40 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1607
  have eq5471 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq5470
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5470
    | exact resolve eq5470 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5470
  have eq5473 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq20 eq5471
    | exact resolve eq5471 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5471
  have eq62785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq5473 eq1604
    | exact resolve eq1604 eq5473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq5473
  have eq62793 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | (have r₁ := eq62785
       have r₂ := eq27
       grind)
    | exact resolve eq62785 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62785
  have eq62818 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq62793 eq255
    | exact resolve eq255 eq62793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq62793
  have eq63002 : y = (k y y) ∨ (σ x) = (σ y) ∨ y = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq62818
    | exact resolve eq62818 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62818
  have eq63003 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq63002
  have eq63043 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq221 X0 y
       have i₂ := eq63003
       grind)
    | exact superpose eq63003 eq221
    | exact resolve eq221 eq63003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq63064 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq937 y X0 X1
       have i₂ := eq63003
       grind)
    | exact superpose eq63003 eq937
    | exact resolve eq937 eq63003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq63095 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1212 y X0
       have i₂ := eq63003
       grind)
    | exact superpose eq63003 eq1212
    | exact resolve eq1212 eq63003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq63098 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1234 y X0
       have i₂ := eq63003
       grind)
    | exact superpose eq63003 eq1234
    | exact resolve eq1234 eq63003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234 eq63003
  have eq63241 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq63098 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63098
    | (have j0 := eq63098 X0
       grind)
    | exact resolve eq63098 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63098
  have eq63243 : ∀ X0 : G, (k X0 X0) = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq63095 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63095
    | (have j0 := eq63095 X0
       grind)
    | exact resolve eq63095 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63095
  have eq63261 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq63064 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63064
    | (have j0 := eq63064 X0 X1
       grind)
    | exact resolve eq63064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63064
  have eq63315 : y = (σ (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63043 eq63241
    | exact resolve eq63241 eq63043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63241
  have eq63317 : y = (σ (σ (σ (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63043 eq63243
    | exact resolve eq63243 eq63043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63243
  have eq63328 : ∀ X1 : G, y = (M.op X1 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X1
    first
    | exact superpose eq63043 eq63261
    | exact resolve eq63261 eq63043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63043 eq63261
  have eq63356 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63315 eq63317
    | exact resolve eq63317 eq63315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63315 eq63317
  have eq63370 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq63356
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63356
    | exact resolve eq63356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63356
  have eq63375 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq63370 eq31
    | exact resolve eq31 eq63370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63463 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq63375
    | exact resolve eq63375 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63375
  have eq63464 : y = (σ y) ∨ x = y := by grind
  clear eq63463
  have eq63466 : (M.op x y) = (M.op x (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq63464
       grind)
    | exact superpose eq63464 eq18
    | exact resolve eq18 eq63464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65871 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63328 eq63466
    | exact resolve eq63466 eq63328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63466
  have eq65872 : y = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63328 eq26
    | (have j1 := eq63328 (σ x)
       grind)
    | exact resolve eq26 eq63328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63328
  have eq65919 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq65871
  have eq65935 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq63370 eq65872
    | exact resolve eq65872 eq63370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63370 eq65872
  have eq66001 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq65935 eq27
    | exact resolve eq27 eq65935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65935
  have eq66095 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq65919 eq31
    | exact resolve eq31 eq65919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65919
  have eq66224 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq66095
    | exact resolve eq66095 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66095
  have eq66225 : y = (M.op x y) ∨ x = y := by grind
  clear eq66224
  have eq66255 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq66225
       grind)
    | exact superpose eq66225 eq24
    | exact resolve eq24 eq66225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66321 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq63464
       have i₂ := eq66225
       grind)
    | exact superpose eq66225 eq63464
    | exact resolve eq63464 eq66225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66322 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq66225
  have eq66323 : (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq66321
       have r₂ := eq66322
       grind)
    | exact resolve eq66321 eq66322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66321
  have eq66377 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq66255
    | exact resolve eq66255 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66255
  have eq66385 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq66323 eq66377
    | exact resolve eq66377 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66377
  have eq66391 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq66323 eq31
    | exact resolve eq31 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq66513 : (σ y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq63464 eq66391
    | exact resolve eq66391 eq63464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63464 eq66391
  have eq66532 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq66323 eq66513
    | exact resolve eq66513 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66513
  have eq66564 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq66385 eq66001
    | exact resolve eq66001 eq66385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66001 eq66385
  have eq66565 : (M.op x y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq66564
  have eq66566 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq66565
       have r₂ := eq66323
       grind)
    | exact resolve eq66565 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66565
  have eq66573 : (M.op x y) = (σ x) ∨ x = y := by
    first
    | exact superpose eq66323 eq66566
    | exact resolve eq66566 eq66323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66323 eq66566
  have eq66579 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq66573 eq29
    | exact resolve eq29 eq66573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq66573
  have eq66607 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq66532 eq66579
    | exact resolve eq66579 eq66532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66532 eq66579
  have eq66616 : x = y := by
    first
    | (have r₁ := eq66607
       have r₂ := eq66322
       grind)
    | exact resolve eq66607 eq66322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66322 eq66607
  have eq66625 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq66616
       grind)
    | exact superpose eq66616 eq18
    | exact resolve eq18 eq66616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq66626 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq66616
       grind)
    | exact superpose eq66616 eq24
    | exact resolve eq24 eq66616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66616
  have eq66689 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq66626
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66626
    | exact resolve eq66626 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66626
  have eq66690 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq66625
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq66625
    | exact resolve eq66625 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66625
  have eq66692 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq66689 eq26
    | exact resolve eq26 eq66689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq66689
  have eq66777 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq66692
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq66692
    | exact resolve eq66692 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq66692
  have eq66783 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq66690
       grind)
    | exact superpose eq66690 eq39
    | exact resolve eq39 eq66690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq66690
  have eq67023 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq66783
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66783
    | exact resolve eq66783 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66783
  have eq67076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66777 eq67023
    | exact resolve eq67023 eq66777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66777 eq67023
  have eq67115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq67076
    | exact resolve eq67076 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq67076
  have eq67133 : False := by grind
  exact eq67133

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq270 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq270 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq270 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq270 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq283 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq271 (σ X0)
       grind)
    | exact superpose eq271 eq15
    | exact resolve eq15 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq271 (τ X0)
       grind)
    | exact superpose eq271 eq17
    | exact resolve eq17 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq295 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq290 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq302 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq283 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq283
    | exact resolve eq283 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq315 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq295 X0
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq295
    | exact resolve eq295 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq295
  have eq353 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq315 X0
       grind)
    | exact superpose eq315 eq10
    | exact resolve eq10 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq414 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq415 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq414 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq414
    | (have j0 := eq414 (σ X0) (σ X1)
       grind)
    | exact resolve eq414 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq2338 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq415 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq415 X0 X1
       grind)
    | exact resolve eq12 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2340 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq415 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq415 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq415 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq415 X0 X1
       grind)
    | exact resolve eq13 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2341 : ∀ X0 X1 X2 X3 : G, (M.op X2 (σ X0)) = (M.op X2 (M.op (M.op (σ X0) (σ X1)) X3)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X3 (σ X0) X2 (σ X1)
       have i₂ := eq415 X0 X1
       grind)
    | (have i₁ := eq63 X0 (σ X1) X2 (σ X0)
       have i₂ := eq415 X0 X1
       grind)
    | exact superpose eq415 eq63
    | (have j1 := eq415 X0 X1
       grind)
    | exact resolve eq63 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq2345 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2340 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2340
  have eq2349 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 (σ X0)) = (M.op X2 (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2341 X0 X1 X2 x
       have i₂ := eq63 x (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq63 eq2341
    | (have j0 := eq2341 X0 X1 X2 x
       grind)
    | exact resolve eq2341 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2341
  have eq2350 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2345 X0 X1
       have i₂ := eq302 X0
       grind)
    | exact superpose eq302 eq2345
    | (have j0 := eq2345 X0 X1
       grind)
    | exact resolve eq2345 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq2345
  have eq2352 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2338 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2338
    | (have j0 := eq2338 X0 X1
       grind)
    | exact resolve eq2338 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2353 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2350 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2350
    | (have j0 := eq2350 X0 X1
       grind)
    | exact resolve eq2350 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2373 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2368 X0 X1
       have j1 := eq2353 X0 X1
       grind)
    | (have r₁ := eq2368 X0 X1
       have r₂ := eq2353 X0 X1
       grind)
    | exact resolve eq2368 eq2353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353 eq2368
  have eq2472 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2349 (τ X0) (τ X1) X2
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq2349
    | (have j0 := eq2349 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq2349 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2349
  have eq2538 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2472 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2472
    | (have j0 := eq2472 X0 X1 X2
       grind)
    | exact resolve eq2472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq2555 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2538 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2538
    | (have j0 := eq2538 X0 X1 X2
       grind)
    | exact resolve eq2538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538
  have eq2560 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 (σ (τ X0))) = (M.op X2 (σ (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2555 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2555
    | (have j0 := eq2555 X0 X1 X2
       grind)
    | exact resolve eq2555 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2565 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (σ (τ X0))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2560 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2560
    | (have j0 := eq2560 X0 X1 X2
       grind)
    | exact resolve eq2560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2570 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2565 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2565
    | (have j0 := eq2565 X0 X1 X2
       grind)
    | exact resolve eq2565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq3149 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2373 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2373
    | exact resolve eq2373 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2373
  have eq3220 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3149 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3149
    | (have j0 := eq3149 X0 X1
       grind)
    | exact resolve eq3149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq3239 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3220 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3220
    | (have j0 := eq3220 X0 X1
       grind)
    | exact resolve eq3220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3220
  have eq3247 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3239 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3239
    | (have j0 := eq3239 X0 X1
       grind)
    | exact resolve eq3239 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3253 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3247 X0 X1
       have i₂ := eq353 X0
       grind)
    | exact superpose eq353 eq3247
    | (have j0 := eq3247 X0 X1
       grind)
    | exact resolve eq3247 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq3247
  have eq3256 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3253 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3253
    | (have j0 := eq3253 X0 X1
       grind)
    | exact resolve eq3253 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253
  have eq3259 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3256 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3256
    | (have j0 := eq3256 X0 X1
       grind)
    | exact resolve eq3256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3409 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3259
  have eq3412 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3409 X0 X1
       have j1 := eq2570 X0 X1 x
       grind)
    | (have r₁ := eq3409 X0 X1
       have r₂ := eq2570 X0 X1 X0
       grind)
    | (have r₁ := eq3409 X1 X0
       have r₂ := eq2570 X0 X1 X1
       grind)
    | exact resolve eq3409 eq2570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570 eq3409
  have eq3471 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3412 X0 X1
       grind)
    | exact superpose eq3412 eq15
    | exact resolve eq15 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3522 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3471 X0 X1
       have i₂ := eq3412 (σ X0) (σ X1)
       grind)
    | exact superpose eq3412 eq3471
    | exact resolve eq3471 eq3412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412 eq3471
  have eq3571 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3522 x y
       grind)
    | exact superpose eq3522 eq16
    | (have r₁ := eq16
       have r₂ := eq3522 x y
       grind)
    | exact resolve eq16 eq3522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq3603 : False := by grind
  exact eq3603

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxx_pyy_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq271 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq271 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq271 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq286 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq272 (σ X0)
       grind)
    | exact superpose eq272 eq15
    | exact resolve eq15 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq272 (τ X0)
       grind)
    | exact superpose eq272 eq17
    | exact resolve eq17 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq298 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq293 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq293
    | exact resolve eq293 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq305 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq286
    | exact resolve eq286 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq318 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq272 X0
       grind)
    | exact superpose eq272 eq298
    | exact resolve eq298 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq298
  have eq341 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (σ X0) X1 (σ X0)
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq63
    | exact resolve eq63 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq10
    | exact resolve eq10 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq363 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X2 (τ X0) X1 (τ X0)
       have i₂ := eq354 X0
       grind)
    | exact superpose eq354 eq63
    | exact resolve eq63 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X0 X1 (τ (M.op X0 X0))
       have i₂ := eq354 (M.op X0 X0)
       grind)
    | exact superpose eq354 eq363
    | exact resolve eq363 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq363
  have eq549 : ∀ X0 X1 : G, (M.op X1 (τ (σ (M.op X0 X0)))) = (M.op X1 (τ (M.op (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq393 (σ (M.op X0 X0)) X1
       have i₂ := eq341 X0 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) (σ (M.op X0 X0))
       grind)
    | exact superpose eq341 eq393
    | exact resolve eq393 eq341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq581 : ∀ X0 X1 : G, (M.op X1 (τ (σ (M.op X0 X0)))) = (M.op X1 (τ (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq305 (M.op X0 X0)
       grind)
    | exact superpose eq305 eq549
    | exact resolve eq549 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq597 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X1 (τ (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq581 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq581
    | exact resolve eq581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq926 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq943 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq926 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq926
    | (have j0 := eq926 X0 X1
       grind)
    | exact resolve eq926 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926
  have eq3852 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (M.op (σ X1) (σ X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq943 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq943
    | (have j0 := eq943 (σ X0) (σ X1)
       grind)
    | exact resolve eq943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq3955 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3852 X0 X1
       have i₂ := eq305 X1
       grind)
    | exact superpose eq305 eq3852
    | (have j0 := eq3852 X0 X1
       grind)
    | exact resolve eq3852 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852
  have eq5596 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (τ (M.op (σ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1)) (σ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq597 (M.op X0 X1) X2
       have i₂ := eq63 (M.op X0 X1) X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       grind)
    | exact superpose eq63 eq597
    | exact resolve eq597 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq5725 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (τ (M.op (σ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1)) (σ (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5596 X0 X1 X2
       have i₂ := eq63 (M.op X0 X1) X1 X2 X0
       grind)
    | exact superpose eq63 eq5596
    | exact resolve eq5596 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5596
  have eq60882 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq342 (σ X0) (σ (σ X1))
       have i₂ := eq3955 X1 X0
       grind)
    | exact superpose eq3955 eq342
    | (have j0 := eq342 (σ X0) (σ (σ X1))
       have j1 := eq3955 X1 X0
       grind)
    | exact resolve eq342 eq3955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq60971 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq3955 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3955
  have eq60974 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq60882 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60882
  have eq61048 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq60974 X0 X1
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq60974
    | (have j0 := eq60974 X0 X1
       grind)
    | exact resolve eq60974 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60974
  have eq61049 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (M.op (σ X0) (σ X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq61048 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61048
  have eq61216 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (k (σ X1) (σ X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61049 X0 X1
       have i₂ := eq15 (σ X1) (σ X0)
       grind)
    | exact superpose eq15 eq61049
    | (have j0 := eq61049 X0 X1
       grind)
    | exact resolve eq61049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61049
  have eq61324 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61216 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq61216
    | (have j0 := eq61216 X0 X1
       grind)
    | exact resolve eq61216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61216
  have eq61398 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61324 X0 X1
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq61324
    | (have j0 := eq61324 X0 X1
       grind)
    | exact resolve eq61324 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61324
  have eq61453 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq61398 X1 X0
       have j1 := eq60971 X0 X1
       grind)
    | (have r₁ := eq61398 X1 X0
       have r₂ := eq60971 X0 X1
       grind)
    | exact resolve eq61398 eq60971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60971 eq61398
  have eq61512 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq61453 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61453
  have eq61606 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (σ (k X1 (τ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61512 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61512
    | exact resolve eq61512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61512
  have eq61859 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ X0)) = (σ (k (σ X1) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq61606 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq61606
    | (have j0 := eq61606 X0 X1
       grind)
    | exact resolve eq61606 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq61606
  have eq62130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61859 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61859
    | exact resolve eq61859 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61859
  have eq62326 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62130 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq62130
    | (have j0 := eq62130 (τ X0) (τ X1)
       grind)
    | exact resolve eq62130 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq62511 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62326 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq62326
    | (have j0 := eq62326 X0 X1
       grind)
    | exact resolve eq62326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62326
  have eq62567 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62511 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62511
    | (have j0 := eq62511 X0 X1
       grind)
    | exact resolve eq62511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62511
  have eq62601 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62567 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq62567
    | (have j0 := eq62567 X0 X1
       grind)
    | exact resolve eq62567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62567
  have eq62634 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq62601 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62601
    | (have j0 := eq62601 X0 X1
       grind)
    | exact resolve eq62601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62601
  have eq62651 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62634 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62634
    | (have j0 := eq62634 X0 X1
       grind)
    | exact resolve eq62634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62634
  have eq62698 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62130 X0 X1
       have i₂ := eq62651 X0 X1
       grind)
    | exact superpose eq62651 eq62130
    | (have j0 := eq62130 X0 X1
       have j1 := eq62651 (σ X0) (σ X1)
       grind)
    | exact resolve eq62130 eq62651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69771 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62698 x y
       grind)
    | exact superpose eq62698 eq16
    | (have j1 := eq62698 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq62698 x y
       grind)
    | exact resolve eq16 eq62698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62698
  have eq69912 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq69771
  have eq70151 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq69912
       grind)
    | exact superpose eq69912 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq69912
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq69912
       grind)
    | exact resolve eq12 eq69912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70153 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 (σ x) X0 (σ y)
       have i₂ := eq69912
       grind)
    | exact superpose eq69912 eq63
    | exact resolve eq63 eq69912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70183 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq70151
  have eq70198 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70183
       have i₂ := eq305 x
       grind)
    | exact superpose eq305 eq70183
    | exact resolve eq70183 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70183
  have eq70214 : (σ (M.op x x)) = (σ (k x y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70198
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq70198
    | exact resolve eq70198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70198
  have eq70217 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq62651 eq70214
    | (have j1 := eq62651 x y
       grind)
    | exact resolve eq70214 eq62651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62651 eq70214
  have eq70220 : (M.op x y) = (τ (σ (M.op x x))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq70217
       grind)
    | exact superpose eq70217 eq10
    | exact resolve eq10 eq70217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70217
  have eq70395 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70220
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq70220
    | exact resolve eq70220 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70220
  have eq70397 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 y X0 x
       have i₂ := eq70395
       grind)
    | exact superpose eq70395 eq63
    | exact resolve eq63 eq70395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70395
  have eq70426 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq70397 X0 x
       have i₂ := eq63 x x X0 x
       grind)
    | exact superpose eq63 eq70397
    | exact resolve eq70397 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70397
  have eq70746 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq70153 X0 (σ x)
       have i₂ := eq69912
       grind)
    | exact superpose eq69912 eq70153
    | exact resolve eq70153 eq69912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69912 eq70153
  have eq71060 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq70746 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70746
  have eq71456 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71060 (σ x)
       grind)
    | exact superpose eq71060 eq16
    | exact resolve eq16 eq71060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71060
  have eq71509 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq71456
       have i₂ := eq305 x
       grind)
    | exact superpose eq305 eq71456
    | exact resolve eq71456 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71456
  have eq71670 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq70426 eq71509
    | exact resolve eq71509 eq70426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70426 eq71509
  have eq71671 : y = (M.op y x) := by grind
  clear eq71670
  have eq71947 : y ≠ y ∨ (M.op x x) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq71671
       grind)
    | exact superpose eq71671 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq71671
       grind)
    | exact resolve eq12 eq71671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71949 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 x X0 y
       have i₂ := eq71671
       grind)
    | exact superpose eq71671 eq63
    | exact resolve eq63 eq71671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq71979 : (M.op x x) = (k x y) := by grind
  clear eq71947
  have eq71983 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq62130 x y
       have i₂ := eq71979
       grind)
    | exact superpose eq71979 eq62130
    | (have j0 := eq62130 x y
       grind)
    | exact resolve eq62130 eq71979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62130 eq71979
  have eq71985 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq71949 X0 x
       have i₂ := eq71671
       grind)
    | exact superpose eq71671 eq71949
    | exact resolve eq71949 eq71671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71949
  have eq72456 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71985 x
       grind)
    | exact superpose eq71985 eq16
    | exact resolve eq16 eq71985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72458 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq341 y X0 X1
       have i₂ := eq71985 y
       grind)
    | exact superpose eq71985 eq341
    | exact resolve eq341 eq71985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq72804 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq72458 X0 X1
       have i₂ := eq71671
       grind)
    | exact superpose eq71671 eq72458
    | exact resolve eq72458 eq71671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72458
  have eq84166 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq72456
       have r₂ := eq71983
       grind)
    | exact resolve eq72456 eq71983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71983
  have eq84205 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (M.op (σ y) (σ y)) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq5725 (σ y) (σ x) x
       have i₂ := eq84166
       grind)
    | exact superpose eq84166 eq5725
    | exact resolve eq5725 eq84166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725
  have eq84218 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (σ (M.op y y)) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq84205 X0
       have i₂ := eq305 y
       grind)
    | exact superpose eq305 eq84205
    | exact resolve eq84205 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84205
  have eq84241 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (σ (M.op y x)) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq84218 X0
       have i₂ := eq71985 y
       grind)
    | exact superpose eq71985 eq84218
    | exact resolve eq84218 eq71985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71985 eq84218
  have eq84258 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (M.op (σ y) (σ x))) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq84241 X0
       have i₂ := eq71671
       grind)
    | exact superpose eq71671 eq84241
    | exact resolve eq84241 eq71671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71671 eq84241
  have eq84271 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (M.op (σ (σ y)) (σ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq84258 X0
       have i₂ := eq84166
       grind)
    | exact superpose eq84166 eq84258
    | exact resolve eq84258 eq84166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84166 eq84258
  have eq84280 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (τ (σ (M.op (σ y) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq84271 X0
       have i₂ := eq305 (σ y)
       grind)
    | exact superpose eq305 eq84271
    | exact resolve eq84271 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84271
  have eq84287 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq84280 X0
       have i₂ := eq10 (M.op (σ y) (σ y))
       grind)
    | exact superpose eq10 eq84280
    | exact resolve eq84280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84280
  have eq84293 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq84287 X0
       have i₂ := eq72804 X0 (σ y)
       grind)
    | exact superpose eq72804 eq84287
    | exact resolve eq84287 eq72804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72804 eq84287
  have eq84305 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72456
       have i₂ := eq84293 (σ x)
       grind)
    | exact superpose eq84293 eq72456
    | exact resolve eq72456 eq84293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72456 eq84293
  have eq84708 : False := by grind
  exact eq84708

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq102 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq102 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq99 X0 X1 X2
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq99 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq99 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq115 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq106 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq106 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq106 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq106 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq120 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109 X0 X1 X2
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq109
    | (have j0 := eq109 X0 X1 X2
       grind)
    | exact resolve eq109 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq123 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       have j1 := eq107 X0 X1
       grind)
    | (have r₁ := eq115 X0 X1
       have r₂ := eq107 X0 X1
       grind)
    | exact resolve eq115 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq115
  have eq392 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq123 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq394 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq392 X0 X1
       have j1 := eq120 X1 X0 x
       grind)
    | (have r₁ := eq392 X0 X1
       have r₂ := eq120 X0 X1 X0
       grind)
    | (have r₁ := eq392 X1 X0
       have r₂ := eq120 X0 X1 X1
       grind)
    | exact resolve eq392 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq392
  have eq412 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq394 (σ X0) (σ X1)
       grind)
    | exact superpose eq394 eq15
    | exact resolve eq15 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 X1
       have i₂ := eq394 X0 X1
       grind)
    | exact superpose eq394 eq412
    | exact resolve eq412 eq394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq412
  have eq629 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq423 x y
       grind)
    | exact superpose eq423 eq16
    | (have r₁ := eq16
       have r₂ := eq423 x y
       grind)
    | exact resolve eq16 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq648 : False := by grind
  exact eq648

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq134 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
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
  have eq142 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq134
    | (have j0 := eq134 X0
       grind)
    | exact resolve eq134 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq144 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq142 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq142
    | (have j0 := eq142 X0
       grind)
    | exact resolve eq142 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq145 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq144 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq144 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq144 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq152 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq145 (σ X0)
       grind)
    | exact superpose eq145 eq15
    | exact resolve eq15 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq152 X0
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq152
    | exact resolve eq152 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq183 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (σ X0) X1 (σ X0)
       have i₂ := eq159 X0
       grind)
    | exact superpose eq159 eq22
    | exact resolve eq22 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq159 X0
       grind)
    | exact superpose eq159 eq9
    | exact resolve eq9 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq1020 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq1066 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1020
    | (have j0 := eq1020 X0 X1
       grind)
    | exact resolve eq1020 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq2113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq335
       have i₂ := eq1066 x y
       grind)
    | exact superpose eq1066 eq335
    | (have j1 := eq1066 (σ x) (σ y)
       grind)
    | (have r₁ := eq335
       have r₂ := eq1066 x y
       grind)
    | (have r₁ := eq335
       have r₂ := eq1066 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq335
       have r₂ := eq1066 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq335 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq2114 : x = y ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq2113
  have eq4405 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (k (σ X0) X1) ∨ (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X2) (k (σ X0) X1)
       have i₂ := eq334 X0 X1 X2
       grind)
    | exact superpose eq334 eq12
    | (have j0 := eq12 (σ X2) (k (σ X0) X1)
       have j1 := eq334 X0 X1 X2
       grind)
    | (have r₁ := eq12 (σ X2) (k (σ X0) X1)
       have r₂ := eq334 X0 X1 X2
       grind)
    | exact resolve eq12 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq4415 : ∀ X0 X1 X2 : G, (k (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4405 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405
  have eq4417 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4415 X0 X1 X2
       have i₂ := eq30 X0 X1 X2
       grind)
    | exact superpose eq30 eq4415
    | (have j0 := eq4415 X0 X1 X2
       grind)
    | exact resolve eq4415 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4415
  have eq4418 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4417 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417
  have eq7393 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (k X1 (τ X2))
       have i₂ := eq4418 X1 X2 (τ X0)
       grind)
    | exact superpose eq4418 eq18
    | (have j1 := eq4418 X1 X2 (τ X0)
       grind)
    | exact resolve eq18 eq4418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4418
  have eq7447 : ∀ X0 X1 X2 : G, (k X0 (σ (k X1 (τ X2)))) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7393 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7393
    | (have j0 := eq7393 X0 X1 X2
       grind)
    | exact resolve eq7393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq7482 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7447 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq7447
    | (have j0 := eq7447 X0 X1 X2
       grind)
    | exact resolve eq7447 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq7447
  have eq7510 : ∀ X0 X1 X2 : G, (k X0 (k (σ X1) X2)) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7482 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7482
    | (have j0 := eq7482 X0 X1 X2
       grind)
    | exact resolve eq7482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7482
  have eq8042 : ∀ X0 X1 X2 : G, (k X1 (k X0 X2)) = (M.op X1 (k X0 X2)) ∨ (k X0 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7510 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7510
    | exact resolve eq7510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8069 : ∀ X0 X1 : G, (k X1 (M.op (σ X0) (σ X0))) = (M.op X1 (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7510 X0 X1 (σ X1)
       have i₂ := eq145 (σ X1)
       grind)
    | exact superpose eq145 eq7510
    | exact resolve eq7510 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7510
  have eq8133 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8069 X0 X1
       have i₂ := eq159 X0
       grind)
    | exact superpose eq159 eq8069
    | (have j0 := eq8069 X0 X1
       grind)
    | exact resolve eq8069 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8069
  have eq8141 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8133 X0 X1
       have i₂ := eq159 X0
       grind)
    | exact superpose eq159 eq8133
    | (have j0 := eq8133 X0 X1
       grind)
    | exact resolve eq8133 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8133
  have eq8406 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8042 X0 X1 X0
       have i₂ := eq145 X0
       grind)
    | exact superpose eq145 eq8042
    | (have j0 := eq8042 X1 (M.op X1 (M.op X0 X0)) (M.op X0 X0)
       grind)
    | exact resolve eq8042 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq8042
  have eq8540 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = (σ (M.op (τ X0) (M.op X1 X1))) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq8406 X1 (τ X0)
       grind)
    | exact superpose eq8406 eq18
    | (have j1 := eq8406 X1 (τ X0)
       grind)
    | exact resolve eq18 eq8406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406
  have eq9645 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (σ (k X0 (M.op X1 X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq8141 X1 (σ X0)
       grind)
    | exact superpose eq8141 eq15
    | (have j1 := eq8141 X1 (σ X0)
       grind)
    | exact resolve eq15 eq8141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8141
  have eq21715 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2114
       grind)
    | exact superpose eq2114 eq16
    | exact resolve eq16 eq2114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2114
  have eq21716 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq21715
       have r₂ := eq159 x
       grind)
    | exact resolve eq21715 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21715
  have eq21920 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 x X0 y
       have i₂ := eq21716
       grind)
    | exact superpose eq21716 eq22
    | exact resolve eq22 eq21716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33940 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (k X0 (M.op X1 X1))) X3)) = (M.op X2 (σ (M.op X1 X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X3 (σ (M.op X1 X1)) X2 (σ X0)
       have i₂ := eq9645 X0 X1
       grind)
    | exact superpose eq9645 eq22
    | (have j1 := eq9645 X0 X1
       grind)
    | exact resolve eq22 eq9645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9645
  have eq59714 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq21920 X0 X1
       grind)
    | exact superpose eq21920 eq12
    | (have j0 := eq12 (σ x) (σ y)
       have j1 := eq21920 X0 X1
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21920 X0 X1
       grind)
    | exact resolve eq12 eq21920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21920
  have eq59731 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq59714 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59714
  have eq59746 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59731 X0 X1
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq59731
    | (have j0 := eq59731 X0 X1
       grind)
    | exact resolve eq59731 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59731
  have eq322849 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq59746 X0 X1
       grind)
    | exact superpose eq59746 eq16
    | (have j1 := eq59746 X0 X1
       grind)
    | exact resolve eq16 eq59746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59746
  have eq324473 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ x = y ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq322849 X0 X1
       have i₂ := eq1066 x y
       grind)
    | exact superpose eq1066 eq322849
    | (have j0 := eq322849 X0 X1
       have j1 := eq1066 x y
       grind)
    | (have r₁ := eq322849 X0 X1
       have r₂ := eq1066 x y
       grind)
    | (have r₁ := eq322849 X0 X1
       have r₂ := eq1066 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq322849 X0 X1
       have r₂ := eq1066 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq322849 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322849
  have eq324474 : ∀ X0 X1 : G, x = y ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq324473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324473
  have eq324478 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq324474 X0 X1
       grind)
    | exact superpose eq324474 eq16
    | (have j1 := eq324474 X0 X1
       grind)
    | exact resolve eq16 eq324474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324474
  have eq324479 : ∀ X0 X1 : G, y = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq324478 X0 X1
       grind)
    | (have r₁ := eq324478 X0 X1
       have r₂ := eq159 x
       grind)
    | exact resolve eq324478 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324478
  have eq326168 : ∀ X0 X1 X2 X3 : G, (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (M.op X2 x) = (M.op X2 (M.op y X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq22 X1 x X0 y
       have i₂ := eq324479 X2 X3
       grind)
    | exact superpose eq324479 eq22
    | (have j1 := eq324479 X0 X1
       grind)
    | exact resolve eq22 eq324479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq324479
  have eq327822 : ∀ X0 X1 X2 X3 : G, y = (τ (σ x)) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (M.op X2 x) = (M.op X2 (M.op y X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10 y
       have i₂ := eq326168 X0 X1 X2 X3
       grind)
    | exact superpose eq326168 eq10
    | (have j1 := eq326168 X0 X1 X0 X1
       grind)
    | exact resolve eq10 eq326168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326168
  have eq328166 : ∀ X0 X1 X2 X3 : G, x = y ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (M.op X2 x) = (M.op X2 (M.op y X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq327822 X0 X1 X2 X3
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq327822
    | (have j0 := eq327822 X0 X1 X0 X1
       grind)
    | exact resolve eq327822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327822
  have eq328183 : ∀ X0 X1 X2 X3 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (M.op X2 x) = (M.op X2 (M.op y X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16
       have i₂ := eq328166 X0 X1 X2 X3
       grind)
    | exact superpose eq328166 eq16
    | (have j1 := eq328166 X0 X1 X0 X1
       grind)
    | exact resolve eq16 eq328166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328166
  have eq328184 : ∀ X0 X1 X2 X3 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) ∨ (M.op X2 x) = (M.op X2 (M.op y X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq328183 X0 X1 X0 X1
       grind)
    | (have r₁ := eq328183 X0 X1 X2 X3
       have r₂ := eq159 x
       grind)
    | exact resolve eq328183 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328183
  have eq330437 : ∀ X0 X1 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq328184 X0 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328184
  have eq330438 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have j0 := eq330437 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330437
  have eq330607 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq330438 X0 x
       have i₂ := eq21716
       grind)
    | exact superpose eq21716 eq330438
    | exact resolve eq330438 eq21716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21716
  have eq330618 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op y X0))) = (M.op X1 (M.op (σ (M.op (M.op y X0) x)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 (M.op y X0) X1 X2
       have i₂ := eq330438 (M.op y X0) X0
       grind)
    | exact superpose eq330438 eq183
    | exact resolve eq183 eq330438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330948 : ∀ X0 : G, (σ (M.op (τ X0) x)) = (k X0 (σ (M.op y y))) ∨ (τ X0) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq8540 X0 y
       have i₂ := eq330438 (τ X0) y
       grind)
    | exact superpose eq330438 eq8540
    | (have j0 := eq8540 X0 y
       grind)
    | exact resolve eq8540 eq330438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8540
  have eq365652 : ∀ X0 : G, (τ (τ X0)) = (M.op y y) ∨ (k X0 (σ (σ (M.op y y)))) = (σ (σ (M.op (τ (τ X0)) x))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op y y))
       have i₂ := eq330948 (τ X0)
       grind)
    | exact superpose eq330948 eq18
    | (have j1 := eq330948 (τ X0)
       grind)
    | exact resolve eq18 eq330948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq330948
  have eq392169 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq330607 X0
       grind)
    | exact superpose eq330607 eq12
    | (have j0 := eq12 (σ x) (σ y)
       have j1 := eq330607 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq330607 X0
       grind)
    | exact resolve eq12 eq330607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330607
  have eq392210 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq392169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392169
  have eq392240 : ∀ X0 : G, (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq392210 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq392210
    | (have j0 := eq392210 X0
       grind)
    | exact resolve eq392210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392210
  have eq496022 : ∀ X0 : G, (k X0 (σ (σ (M.op y y)))) = (σ (σ (M.op (τ (τ X0)) x))) ∨ (τ X0) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq11 (τ X0)
       have i₂ := eq365652 X0
       grind)
    | exact superpose eq365652 eq11
    | (have j1 := eq365652 X0
       grind)
    | exact resolve eq11 eq365652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365652
  have eq501938 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq392240 X0
       grind)
    | exact superpose eq392240 eq16
    | (have j1 := eq392240 X0
       grind)
    | exact resolve eq16 eq392240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392240
  have eq502076 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op X0 x) = (M.op X0 y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq501938 X0
       have i₂ := eq1066 x y
       grind)
    | exact superpose eq1066 eq501938
    | (have j0 := eq501938 X0
       have j1 := eq1066 x y
       grind)
    | (have r₁ := eq501938 X0
       have r₂ := eq1066 x y
       grind)
    | (have r₁ := eq501938 X0
       have r₂ := eq1066 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq501938 X0
       have r₂ := eq1066 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq501938 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq501938
  have eq502077 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 x) = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq502076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502076
  have eq504195 : ∀ X0 X1 : G, x = y ∨ (M.op X1 x) = (M.op X1 y) ∨ (M.op X0 x) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq330438 X1 x
       have i₂ := eq502077 X0
       grind)
    | exact superpose eq502077 eq330438
    | (have j1 := eq502077 X1
       grind)
    | exact resolve eq330438 eq502077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502077
  have eq555384 : ∀ X0 : G, (k X0 (τ (σ (σ (M.op y y))))) = (τ (σ (σ (M.op (τ (τ (σ X0))) x)))) ∨ (τ (σ X0)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ (σ (M.op y y)))
       have i₂ := eq496022 (σ X0)
       grind)
    | exact superpose eq496022 eq32
    | (have j1 := eq496022 (σ X0)
       grind)
    | exact resolve eq32 eq496022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496022
  have eq555909 : ∀ X0 : G, (σ (M.op (τ (τ (σ X0))) x)) = (k X0 (τ (σ (σ (M.op y y))))) ∨ (τ (σ X0)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq555384 X0
       have i₂ := eq10 (σ (M.op (τ (τ (σ X0))) x))
       grind)
    | exact superpose eq10 eq555384
    | (have j0 := eq555384 X0
       grind)
    | exact resolve eq555384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555384
  have eq556158 : ∀ X0 : G, (k X0 (σ (M.op y y))) = (σ (M.op (τ (τ (σ X0))) x)) ∨ (τ (σ X0)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq555909 X0
       have i₂ := eq10 (σ (M.op y y))
       grind)
    | exact superpose eq10 eq555909
    | (have j0 := eq555909 X0
       grind)
    | exact resolve eq555909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555909
  have eq556335 : ∀ X0 : G, (σ (M.op (τ X0) x)) = (k X0 (σ (M.op y y))) ∨ (τ (σ X0)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq556158 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq556158
    | (have j0 := eq556158 X0
       grind)
    | exact resolve eq556158 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556158
  have eq556439 : ∀ X0 : G, (σ (M.op (τ X0) x)) = (k X0 (σ (M.op y y))) ∨ (σ (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq556335 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq556335
    | (have j0 := eq556335 X0
       grind)
    | exact resolve eq556335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556335
  have eq559222 : ∀ X0 : G, (k X0 (τ (σ (M.op y y)))) = (τ (σ (M.op (τ (σ X0)) x))) ∨ (σ X0) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ (M.op y y))
       have i₂ := eq556439 (σ X0)
       grind)
    | exact superpose eq556439 eq32
    | (have j1 := eq556439 (σ X0)
       grind)
    | exact resolve eq32 eq556439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq556439
  have eq559950 : ∀ X0 : G, (k X0 (τ (σ (M.op y y)))) = (M.op (τ (σ X0)) x) ∨ (σ X0) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq559222 X0
       have i₂ := eq10 (M.op (τ (σ X0)) x)
       grind)
    | exact superpose eq10 eq559222
    | (have j0 := eq559222 X0
       grind)
    | exact resolve eq559222 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559222
  have eq560167 : ∀ X0 : G, (M.op X0 x) = (k X0 (τ (σ (M.op y y)))) ∨ (σ X0) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq559950 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq559950
    | (have j0 := eq559950 X0
       grind)
    | exact resolve eq559950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559950
  have eq560294 : ∀ X0 : G, (M.op X0 x) = (k X0 (M.op y y)) ∨ (σ X0) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq560167 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq560167
    | (have j0 := eq560167 X0
       grind)
    | exact resolve eq560167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560167
  have eq560436 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op y y))) = (M.op X1 (M.op (σ (M.op X0 x)) X2)) ∨ (σ X0) = (σ (M.op y y)) ∨ (σ X0) = (σ (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33940 X0 y X1 X2
       have i₂ := eq560294 X0
       grind)
    | exact superpose eq560294 eq33940
    | (have j0 := eq33940 X0 y X2 x
       have j1 := eq560294 X0
       grind)
    | exact resolve eq33940 eq560294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33940 eq560294
  have eq561036 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op y y))) = (M.op X1 (M.op (σ (M.op X0 x)) X2)) ∨ (σ X0) = (σ (M.op y y)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq560436 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560436
  have eq637141 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 x) = (M.op X0 y) ∨ (M.op X1 x) = (M.op X1 y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq504195 X0 X1
       grind)
    | exact superpose eq504195 eq16
    | (have j1 := eq504195 X0 X0
       grind)
    | exact resolve eq16 eq504195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504195
  have eq637285 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X1 x) = (M.op X1 y) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have j0 := eq637141 X1 X1
       grind)
    | (have r₁ := eq637141 X0 X1
       have r₂ := eq159 x
       grind)
    | exact resolve eq637141 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637141
  have eq637297 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 x) = (M.op X0 y) ∨ (M.op X1 x) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq637285 X1 X0
       grind)
    | exact superpose eq637285 eq10
    | (have j1 := eq637285 X0 X0
       grind)
    | exact resolve eq10 eq637285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637285
  have eq637650 : ∀ X0 X1 : G, x = y ∨ (M.op X0 x) = (M.op X0 y) ∨ (M.op X1 x) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq637297 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq637297
    | (have j0 := eq637297 X0 X0
       grind)
    | exact resolve eq637297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637297
  have eq639921 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 x) = (M.op X0 y) ∨ (M.op X1 x) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq637650 X0 X1
       grind)
    | exact superpose eq637650 eq16
    | (have j1 := eq637650 X0 X0
       grind)
    | exact resolve eq16 eq637650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637650
  have eq640065 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 y) ∨ (M.op X1 x) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq639921 X0 X0
       grind)
    | (have r₁ := eq639921 X0 X1
       have r₂ := eq159 x
       grind)
    | exact resolve eq639921 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639921
  have eq640595 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq640065 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640065
  have eq640596 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq640595 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640595
  have eq643009 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq185 y X0
       have i₂ := eq640596 y
       grind)
    | exact superpose eq640596 eq185
    | exact resolve eq185 eq640596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215854 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y y))) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq185 x X0
       have i₂ := eq561036 x X0 X0
       grind)
    | exact superpose eq561036 eq185
    | (have j1 := eq561036 x x x
       grind)
    | exact resolve eq185 eq561036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1215859 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq643009 X0
       have i₂ := eq561036 y X0 X0
       grind)
    | exact superpose eq561036 eq643009
    | (have j1 := eq561036 y x x
       grind)
    | exact resolve eq643009 eq561036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561036 eq643009
  have eq1216752 : ∀ X0 : G, (M.op X0 (σ (M.op y x))) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1215859 X0
       have i₂ := eq640596 y
       grind)
    | exact superpose eq640596 eq1215859
    | exact resolve eq1215859 eq640596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215859
  have eq1216757 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ (σ x) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq1215854 X0
       have i₂ := eq640596 y
       grind)
    | exact superpose eq640596 eq1215854
    | exact resolve eq1215854 eq640596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215854
  have eq1217292 : ∀ X0 : G, (σ y) = (σ (M.op y x)) ∨ (M.op X0 (σ (M.op y x))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1216752 X0
       have i₂ := eq640596 y
       grind)
    | exact superpose eq640596 eq1216752
    | (have j0 := eq1216752 X0
       grind)
    | exact resolve eq1216752 eq640596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216752
  have eq1217297 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq1216757 X0
       have i₂ := eq640596 y
       grind)
    | exact superpose eq640596 eq1216757
    | (have j0 := eq1216757 X0
       grind)
    | exact resolve eq1216757 eq640596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216757
  have eq1217912 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op (M.op y x) (M.op y x))) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq159 (M.op y x)
       have i₂ := eq1217297 X0
       grind)
    | exact superpose eq1217297 eq159
    | (have j1 := eq1217297 X0
       grind)
    | exact resolve eq159 eq1217297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217297
  have eq1218285 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op (M.op y x) x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq1217912 X0
       have i₂ := eq330438 (M.op y x) x
       grind)
    | exact superpose eq330438 eq1217912
    | (have j0 := eq1217912 X0
       grind)
    | exact resolve eq1217912 eq330438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330438 eq1217912
  have eq1218327 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op (M.op y x) x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq1218285 X0
       have i₂ := eq159 x
       grind)
    | exact superpose eq159 eq1218285
    | (have j0 := eq1218285 X0
       grind)
    | exact resolve eq1218285 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218285
  have eq1428478 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op y x))) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (M.op X2 (σ x)) = (M.op X2 (σ (M.op y x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq330618 x X0 X1
       have i₂ := eq1218327 X2
       grind)
    | exact superpose eq1218327 eq330618
    | (have j1 := eq1218327 X2
       grind)
    | exact resolve eq330618 eq1218327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330618 eq1218327
  have eq1428985 : ∀ X0 X2 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ (M.op X2 (σ x)) = (M.op X2 (σ (M.op y x))) := by
    intro X0 X2
    first
    | (have i₁ := eq1428478 X0 x X2
       have i₂ := eq183 x X0 x
       grind)
    | exact superpose eq183 eq1428478
    | (have j0 := eq1428478 X0 x X0
       grind)
    | exact resolve eq1428478 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq1428478
  have eq1456788 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have j0 := eq1428985 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428985
  have eq1456789 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
    intro X0
    first
    | (have j0 := eq1456788 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456788
  have eq1459263 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (M.op X1 (σ y)) = (M.op X1 (σ (M.op y x))) := by
    intro X0 X1
    first
    | (have i₁ := eq1456789 X0
       have i₂ := eq1217292 X1
       grind)
    | exact superpose eq1217292 eq1456789
    | (have j1 := eq1217292 X1
       grind)
    | exact resolve eq1456789 eq1217292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217292
  have eq1460154 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X1 (σ y)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1459263 X0 X1
       have i₂ := eq1456789 X1
       grind)
    | exact superpose eq1456789 eq1459263
    | (have j0 := eq1459263 X1 X1
       grind)
    | exact resolve eq1459263 eq1456789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1456789 eq1459263
  have eq1482982 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1460154 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460154
  have eq1482983 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1482982 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482982
  have eq1483420 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1482983 (σ x)
       grind)
    | exact superpose eq1482983 eq16
    | exact resolve eq16 eq1482983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482983
  have eq1483694 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1483420
       have i₂ := eq159 x
       grind)
    | exact superpose eq159 eq1483420
    | exact resolve eq1483420 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1483420
  have eq1483877 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1483694
       have i₂ := eq640596 x
       grind)
    | exact superpose eq640596 eq1483694
    | exact resolve eq1483694 eq640596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640596 eq1483694
  have eq1483878 : False := by grind
  exact eq1483878

/-- `Equation3532`: `x ◇ y = x ◇ ((z ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pxy_pxx_pxy_Equation3532 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3532 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3532.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X2 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X3 X1) X0) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X3 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X1 X2 X3
       have i₂ := eq9 X2 X1 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq35 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq45
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq95 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq105 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq98 (σ X0)
       grind)
    | exact superpose eq98 eq32
    | exact resolve eq32 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq98 (τ X0)
       grind)
    | exact superpose eq98 eq36
    | exact resolve eq36 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq107 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq98 (τ X0)
       grind)
    | exact superpose eq98 eq18
    | exact resolve eq18 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq108 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq109 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq106 X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq106
    | exact resolve eq106 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq110 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq108
    | exact resolve eq108 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq110
    | exact resolve eq110 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq110
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq116 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq137 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 x y
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 x y
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq293 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op (σ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X2 (σ X0) X1 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq26
    | exact resolve eq26 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq35
    | exact resolve eq35 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq109
  have eq304 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq303 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq303
    | exact resolve eq303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq305 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq304
  have eq311 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq305 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq305
    | exact resolve eq305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq337 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq311
    | exact resolve eq311 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq311
  have eq344 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq337 X0
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq337
    | exact resolve eq337 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq519 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq137
       have i₂ := eq120 y
       grind)
    | exact superpose eq120 eq137
    | exact resolve eq137 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq520 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq519
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq519
    | exact resolve eq519 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq521 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq520
       have i₂ := eq120 y
       grind)
    | exact superpose eq120 eq520
    | exact resolve eq520 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq522 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq521
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq521
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq521 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq523 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq522
  have eq8697 : (M.op y y) = (τ (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq523
       grind)
    | exact superpose eq523 eq10
    | exact resolve eq10 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq8738 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq8697
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8697
    | exact resolve eq8697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8697
  have eq8739 : x = (M.op y y) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq8738
  have eq96679 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq344 y
       have i₂ := eq8739
       grind)
    | exact superpose eq8739 eq344
    | exact resolve eq344 eq8739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq8739
  have eq96767 : (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq96679
       have r₂ := eq16
       grind)
    | exact resolve eq96679 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96679
  have eq97249 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 y X0 X1
       have i₂ := eq96767
       grind)
    | exact superpose eq96767 eq293
    | exact resolve eq293 eq96767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97331 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X1 y X0 y
       have i₂ := eq96767
       grind)
    | exact superpose eq96767 eq26
    | exact resolve eq26 eq96767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96767
  have eq97339 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq97331 X0 x
       have i₂ := eq26 x x X0 x
       grind)
    | exact superpose eq26 eq97331
    | exact resolve eq97331 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97331
  have eq97353 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq97249 X0 x
       have i₂ := eq293 x X0 x
       grind)
    | exact superpose eq293 eq97249
    | exact resolve eq97249 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97249
  have eq97782 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq97339 X0
       grind)
    | exact superpose eq97339 eq10
    | (have j1 := eq97339 X0
       grind)
    | exact resolve eq10 eq97339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97339
  have eq98001 : ∀ X0 : G, (M.op y y) = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq97782 X0
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq97782
    | (have j0 := eq97782 X0
       grind)
    | exact resolve eq97782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97782
  have eq98617 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x x) X1)) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X1 y X0 y
       have i₂ := eq98001 X2
       grind)
    | exact superpose eq98001 eq26
    | (have j1 := eq98001 X2
       grind)
    | exact resolve eq26 eq98001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98001
  have eq98626 : ∀ X0 X2 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X2 y) = (M.op X2 x) := by
    intro X0 X2
    first
    | (have i₁ := eq98617 X0 x X2
       have i₂ := eq26 x x X0 x
       grind)
    | exact superpose eq26 eq98617
    | (have j0 := eq98617 X0 x X0
       grind)
    | exact resolve eq98617 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq98617
  have eq99812 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq98626 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98626
  have eq99813 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq99812 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99812
  have eq100249 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op y x)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq293 y X0 X1
       have i₂ := eq99813 y
       grind)
    | exact superpose eq99813 eq293
    | exact resolve eq293 eq99813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176693 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq97353 X0
       have i₂ := eq99813 y
       grind)
    | exact superpose eq99813 eq97353
    | (have j0 := eq97353 X0
       grind)
    | exact resolve eq97353 eq99813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97353
  have eq177553 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) ∨ (M.op X2 (σ y)) = (M.op X2 (σ x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100249 X0 X1
       have i₂ := eq176693 X2
       grind)
    | exact superpose eq176693 eq100249
    | (have j1 := eq176693 X2
       grind)
    | exact resolve eq100249 eq176693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100249 eq176693
  have eq177883 : ∀ X0 X2 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) ∨ (M.op X2 (σ y)) = (M.op X2 (σ x)) := by
    intro X0 X2
    first
    | (have i₁ := eq177553 X0 x X2
       have i₂ := eq293 x X0 x
       grind)
    | exact superpose eq293 eq177553
    | (have j0 := eq177553 X0 x X0
       grind)
    | exact resolve eq177553 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq177553
  have eq199297 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq177883 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177883
  have eq199298 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq199297 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199297
  have eq200283 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199298 (σ x)
       grind)
    | exact superpose eq199298 eq16
    | exact resolve eq16 eq199298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199298
  have eq200450 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq200283
       have i₂ := eq120 x
       grind)
    | exact superpose eq120 eq200283
    | exact resolve eq200283 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq200283
  have eq200740 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq200450
       have i₂ := eq99813 x
       grind)
    | exact superpose eq99813 eq200450
    | exact resolve eq200450 eq99813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99813 eq200450
  have eq200741 : False := by grind
  exact eq200741
