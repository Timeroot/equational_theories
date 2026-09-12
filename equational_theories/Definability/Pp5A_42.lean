import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_x_x_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  clear eq43
  have eq50 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq216 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq61 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq62 x x
       have i₂ := eq61 x x
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq226 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq225 eq14
    | exact resolve eq14 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq226 x x
       have i₂ := eq61 x x
       grind)
    | exact superpose eq61 eq226
    | exact resolve eq226 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq245 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq655 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 (σ X0)
       have i₂ := eq99 X0 X0
       grind)
    | exact superpose eq99 eq73
    | (have j0 := eq73 X1 (σ X0)
       have j1 := eq99 X0 X0
       grind)
    | (have r₁ := eq73 X0 (σ X1)
       have r₂ := eq99 X0 X1
       grind)
    | (have r₁ := eq73 X0 (σ X0)
       have r₂ := eq99 X0 X0
       grind)
    | exact resolve eq73 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq99 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq659 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq661 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq655 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq666 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq661 X0 X1
       have j1 := eq73 X1 (σ X0)
       grind)
    | (have r₁ := eq661 X0 X1
       have r₂ := eq73 X0 (σ X0)
       grind)
    | exact resolve eq661 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq3922 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq659 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq659
    | (have j0 := eq659 (τ X0)
       grind)
    | exact resolve eq659 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq659
  have eq3942 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3922 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3922
    | (have j0 := eq3922 X0
       grind)
    | exact resolve eq3922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq3953 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3942 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3942
    | (have j0 := eq3942 X0
       grind)
    | exact resolve eq3942 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3942
  have eq10634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq10635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10634
    | exact resolve eq10634 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10634
  have eq10646 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10635
       have r₂ := eq27
       grind)
    | exact resolve eq10635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10635
  have eq10648 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10646
    | exact resolve eq10646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10646
  have eq10659 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10648 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq10648
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10648
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10648
       grind)
    | exact resolve eq13 eq10648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10648
  have eq10660 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq10659
  have eq10800 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq10660 eq49
    | exact resolve eq49 eq10660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10660
  have eq10840 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq10800
    | exact resolve eq10800 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10800
  have eq10844 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq3953 x
       grind)
    | (have r₁ := eq10840
       have r₂ := eq3953 x
       grind)
    | exact resolve eq10840 eq3953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953 eq10840
  have eq10846 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq73 X0 x
       have i₂ := eq10844
       grind)
    | exact superpose eq10844 eq73
    | (have j0 := eq73 X0 x
       grind)
    | (have r₁ := eq73 X0 x
       have r₂ := eq10844
       grind)
    | exact resolve eq73 eq10844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq10844
  have eq10854 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10846 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10846
  have eq11057 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq79
       have i₂ := eq10854 y
       grind)
    | exact superpose eq10854 eq79
    | exact resolve eq79 eq10854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq10854
  have eq11135 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11057
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11057
    | exact resolve eq11057 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11057
  have eq11166 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11135
       have r₂ := eq51
       grind)
    | exact resolve eq11135 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq11135
  have eq11176 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11166 eq86
    | exact resolve eq86 eq11166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq11166
  have eq11199 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq11176
    | exact resolve eq11176 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11176
  have eq11203 : y = (k y x) := by
    first
    | (have r₁ := eq11199
       have r₂ := eq50
       grind)
    | exact resolve eq11199 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11199
  have eq11343 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq658 x y
       have i₂ := eq11203
       grind)
    | exact superpose eq11203 eq658
    | (have j0 := eq658 x x
       grind)
    | exact resolve eq658 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11344 : y = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq11203
       grind)
    | exact superpose eq11203 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11203
  have eq11345 : y = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq11344
  have eq11346 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11343
  have eq11348 : x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11345
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11345
    | exact resolve eq11345 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11345
  have eq11349 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11346
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11346
    | exact resolve eq11346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11346
  have eq11359 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11349
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11349
    | exact resolve eq11349 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11349
  have eq11361 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11359
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11359
    | exact resolve eq11359 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11359
  have eq11363 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11361
    | exact resolve eq11361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11361
  have eq11395 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x
       have i₂ := eq11348
       grind)
    | exact superpose eq11348 eq61
    | exact resolve eq61 eq11348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11402 : x ≠ x ∨ x = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq11348
       grind)
    | exact superpose eq11348 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq11348
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq11348
       grind)
    | exact resolve eq13 eq11348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11403 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq11402
  have eq11551 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11363 eq61
    | exact resolve eq61 eq11363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11558 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11363 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq11363
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq11363
       grind)
    | exact resolve eq13 eq11363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11559 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11558
  have eq11727 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq666 x X0
       have i₂ := eq11403
       grind)
    | exact superpose eq11403 eq666
    | (have j0 := eq666 x X0
       grind)
    | exact resolve eq666 eq11403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11731 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq658 x x
       have i₂ := eq11403
       grind)
    | exact superpose eq11403 eq658
    | (have j0 := eq658 x x
       grind)
    | exact resolve eq658 eq11403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq11403
  have eq11734 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11731
  have eq11735 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq11734
  have eq11739 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq11727 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11727
  have eq11744 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11735
    | exact resolve eq11735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11735
  have eq11746 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11739 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11739
    | (have j0 := eq11739 X0
       grind)
    | exact resolve eq11739 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11739
  have eq12049 : (τ (σ x)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11559 eq49
    | exact resolve eq49 eq11559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq11559
  have eq12089 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq12049
    | exact resolve eq12049 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12049
  have eq12293 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11744 eq61
    | exact resolve eq61 eq11744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12356 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (k X0 (σ (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11746 eq666
    | (have j0 := eq666 (σ x) X0
       grind)
    | exact resolve eq666 eq11746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666 eq11746
  have eq12381 : ∀ X0 : G, (k X0 (σ (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12356
  have eq12468 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq12089
       grind)
    | exact superpose eq12089 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq12089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12089
  have eq12469 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12468
  have eq12663 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x
       have i₂ := eq12469
       grind)
    | exact superpose eq12469 eq61
    | exact resolve eq61 eq12469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12874 : (σ (M.op x y)) = (σ (k (M.op x y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq12381
    | exact resolve eq12381 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq12381
  have eq14129 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11395 eq11395
    | exact resolve eq11395 eq11395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11395
  have eq14171 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq14129 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14129
  have eq14489 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11551 eq11363
    | exact resolve eq11363 eq11551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11363 eq11551
  have eq14492 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14489
  have eq14509 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14492 eq228
    | exact resolve eq228 eq14492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14549 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14509
    | exact resolve eq14509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14509
  have eq14686 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14549 eq27
    | exact resolve eq27 eq14549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14549
  have eq17278 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11348
       have i₂ := eq14171 x X0
       grind)
    | (have i₁ := eq11348
       have i₂ := eq14171 X0 x
       grind)
    | exact superpose eq14171 eq11348
    | exact resolve eq11348 eq14171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11348 eq14171
  have eq17283 : ∀ X0 : G, x = (M.op X0 x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17278 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17278
  have eq17319 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17283 (M.op x x)
       have i₂ := eq216 x x
       grind)
    | exact superpose eq216 eq17283
    | exact resolve eq17283 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17336 : ∀ X0 : G, x ≠ x ∨ x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 x X0
       have i₂ := eq17283 X0
       grind)
    | exact superpose eq17283 eq13
    | (have j0 := eq13 x X0
       grind)
    | (have r₁ := eq13 x X0
       have r₂ := eq17283 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17283 X0
       grind)
    | exact resolve eq13 eq17283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17283
  have eq17343 : ∀ X0 : G, x = (k x X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17336 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17336
  have eq17396 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq17319 eq14
    | exact resolve eq14 eq17319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17400 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq17396 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17396
    | (have j0 := eq17396 X0 X1
       grind)
    | exact resolve eq17396 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17396
  have eq17413 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17400 x x
       have i₂ := eq61 x x
       grind)
    | exact superpose eq61 eq17400
    | exact resolve eq17400 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq17400
  have eq17735 : ∀ X0 : G, x = (τ (k (σ x) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17343 (τ X0)
       have i₂ := eq245 X0
       grind)
    | exact superpose eq245 eq17343
    | exact resolve eq17343 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq17343
  have eq38583 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12293 eq11744
    | exact resolve eq11744 eq12293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11744 eq12293
  have eq38590 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq38583
  have eq39041 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38590 eq228
    | exact resolve eq228 eq38590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq39066 : x = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38590 eq17319
    | exact resolve eq17319 eq38590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39067 : (M.op x y) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38590 eq17413
    | exact resolve eq17413 eq38590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17413 eq38590
  have eq39076 : (M.op x y) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq39067
  have eq39077 : y = (M.op x y) ∨ x = (σ x) := by grind
  clear eq39066
  have eq39094 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq39041
    | exact resolve eq39041 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39041
  have eq39095 : (σ y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq39077 eq20
    | exact resolve eq20 eq39077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39077
  have eq39284 : (σ (M.op x y)) = (σ y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq39095
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39095
    | exact resolve eq39095 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39095
  have eq39729 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39094 eq27
    | exact resolve eq27 eq39094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39731 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39094 eq225
    | exact resolve eq225 eq39094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq39094
  have eq39754 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq39731
    | exact resolve eq39731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39731
  have eq39863 : ∀ X0 : G, x = (τ (k (M.op x y) X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39076 eq17735
    | exact resolve eq17735 eq39076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17735 eq39076
  have eq39876 : ∀ X0 : G, x = (τ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq39863 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39863
  have eq43958 : x = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39754 eq17319
    | exact resolve eq17319 eq39754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17319 eq39754
  have eq43971 : y = (M.op x y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq43958
  have eq44444 : (σ y) = (σ (M.op x y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43971 eq20
    | exact resolve eq20 eq43971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43971
  have eq44641 : (σ (M.op x y)) = (σ y) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44444
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44444
    | exact resolve eq44444 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44444
  have eq45152 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44641 eq14686
    | (have r₁ := eq14686
       have r₂ := eq44641
       grind)
    | exact resolve eq14686 eq44641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14686 eq44641
  have eq45163 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq45152
  have eq45263 : x ≠ (σ x) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq45163
  have eq74511 : ∀ X0 : G, (σ x) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39876 eq15
    | exact resolve eq15 eq39876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39876
  have eq74671 : ∀ X0 : G, (σ x) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74511 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq74511
    | (have j0 := eq74511 X0
       grind)
    | exact resolve eq74511 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74511
  have eq74912 : (σ (M.op x y)) = (σ (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq74671 eq12874
    | exact resolve eq12874 eq74671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12874 eq74671
  have eq74930 : (σ (M.op x y)) = (σ (σ x)) ∨ y = (M.op x y) := by grind
  clear eq74912
  have eq120342 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12663 eq14492
    | exact resolve eq14492 eq12663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12663 eq14492
  have eq120389 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq120342 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120342
  have eq120454 : x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12469
       have i₂ := eq120389 x
       grind)
    | exact superpose eq120389 eq12469
    | exact resolve eq12469 eq120389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12469 eq120389
  have eq120469 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq120454
  have eq120497 : (σ (M.op x y)) ≠ (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq120469 eq27
    | exact resolve eq27 eq120469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120469
  have eq120606 : x = (σ x) := by
    first
    | (have r₁ := eq120497
       have r₂ := eq39284
       grind)
    | exact resolve eq120497 eq39284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39284 eq120497
  have eq121354 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq120606 eq26
    | exact resolve eq26 eq120606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq121501 : x ≠ x ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120606 eq45263
    | (have r₁ := eq45263
       have r₂ := eq120606
       grind)
    | exact resolve eq45263 eq120606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45263
  have eq121513 : (σ x) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120606 eq74930
    | exact resolve eq74930 eq120606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74930
  have eq121524 : x = (M.op (σ x) (σ y)) := by grind
  clear eq121501
  have eq121535 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq121513
    | exact resolve eq121513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121513
  have eq121565 : y = (M.op x y) := by
    first
    | (have r₁ := eq121535
       have r₂ := eq39729
       grind)
    | exact resolve eq121535 eq39729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39729 eq121535
  have eq121572 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq121565 eq20
    | exact resolve eq20 eq121565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq121899 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq121572
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq121572
    | exact resolve eq121572 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121572
  have eq122033 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq121524 eq27
    | exact resolve eq27 eq121524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq122747 : (M.op (σ x) (σ y)) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq121899 eq121354
    | exact resolve eq121354 eq121899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121354
  have eq122748 : x = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq121524 eq122747
    | exact resolve eq122747 eq121524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121524 eq122747
  have eq124149 : (M.op (M.op x y) y) = (M.op x (σ (M.op x y))) := by
    first
    | exact superpose eq122748 eq216
    | exact resolve eq216 eq122748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124157 : x = (M.op (M.op x y) y) := by
    first
    | exact superpose eq122748 eq124149
    | exact resolve eq124149 eq122748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122748 eq124149
  have eq124161 : x = (M.op y y) := by
    first
    | exact superpose eq121565 eq124157
    | exact resolve eq124157 eq121565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124157
  have eq124227 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq216 y y
       have i₂ := eq124161
       grind)
    | exact superpose eq124161 eq216
    | exact resolve eq216 eq124161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq124239 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq121565 eq124227
    | exact resolve eq124227 eq121565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124227
  have eq124247 : x = (M.op x y) := by
    first
    | (have i₁ := eq124239
       have i₂ := eq124161
       grind)
    | exact superpose eq124161 eq124239
    | exact resolve eq124239 eq124161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124161 eq124239
  have eq124255 : x = (M.op x y) := by
    first
    | (have i₁ := eq124247
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124247
    | exact resolve eq124247 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq124247
  have eq124262 : x = y := by
    first
    | exact superpose eq121565 eq124255
    | exact resolve eq124255 eq121565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121565 eq124255
  have eq124268 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq124262
       grind)
    | exact superpose eq124262 eq24
    | exact resolve eq24 eq124262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq124262
  have eq124651 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq121899 eq124268
    | exact resolve eq124268 eq121899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121899 eq124268
  have eq124824 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq124651
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124651
    | exact resolve eq124651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq124651
  have eq124973 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq120606 eq124824
    | exact resolve eq124824 eq120606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120606 eq124824
  have eq125050 : False := by grind
  exact eq125050

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq63 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq210 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq64 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq220 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq219 eq14
    | exact resolve eq14 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq220 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq220
    | exact resolve eq220 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq307 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq467 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq63 x x X2 X3 X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq468 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq467 x x X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq467
    | exact resolve eq467 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq477 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = X0 ∨ (k (M.op (M.op x y) y) X0) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq468 eq12
    | (have j0 := eq12 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op x y) y) x
       have r₂ := eq468 (M.op (M.op x y) y)
       grind)
    | exact resolve eq12 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op (M.op x y) y) X0) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq477 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq491 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq468 eq486
    | (have j0 := eq486 X0
       grind)
    | exact resolve eq486 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq492 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq491 X0
       have j1 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq491 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq491 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq619 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq78 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq626 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq628 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq637 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq628 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq628 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq628 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq672 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq307
    | exact resolve eq307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq1237 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq637 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq637
    | (have j0 := eq637 (τ X0) X1
       grind)
    | exact resolve eq637 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq1257 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1237 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1237
    | (have j0 := eq1237 X0 X1
       grind)
    | exact resolve eq1237 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237
  have eq1268 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1257 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1257
    | (have j0 := eq1257 X0 X1
       grind)
    | exact resolve eq1257 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1288 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1268 (τ X0) X1
       have i₂ := eq672 X0 X0
       grind)
    | exact superpose eq672 eq1268
    | (have j0 := eq1268 (τ X0) X1
       grind)
    | exact resolve eq1268 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq1268
  have eq3861 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq492 eq626
    | (have j0 := eq626 (M.op (M.op x y) y)
       grind)
    | exact resolve eq626 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq3877 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq626 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq626
    | (have j0 := eq626 (τ X0)
       grind)
    | exact resolve eq626 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3893 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq3861
  have eq3897 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3877 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3877
    | (have j0 := eq3877 X0
       grind)
    | exact resolve eq3877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3877
  have eq3908 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3897 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3897
    | (have j0 := eq3897 X0
       grind)
    | exact resolve eq3897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq16931 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq3893 eq210
    | exact resolve eq210 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq16941 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3893 eq16931
    | exact resolve eq16931 eq3893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893 eq16931
  have eq16993 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq16941 eq16
    | exact resolve eq16 eq16941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq17564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq17563
    | exact resolve eq17563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17563
  have eq17575 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq17564
       have r₂ := eq27
       grind)
    | exact resolve eq17564 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17564
  have eq17582 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17575 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq17575
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq17575
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq17575
       grind)
    | exact resolve eq13 eq17575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17575
  have eq17587 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq17582 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17582
  have eq17598 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq17587 (M.op X1 X1)
       grind)
    | exact superpose eq17587 eq13
    | (have j0 := eq13 X0 (σ x)
       have j1 := eq17587 X1
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq17587 X0
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq17587 X0
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq17587 X0
       grind)
    | exact resolve eq13 eq17587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17587
  have eq17603 : ∀ X0 X1 : G, y = (M.op y y) ∨ (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have j0 := eq17598 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17598
  have eq17894 : ∀ X0 X1 X2 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ x = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq17603 X2 X1
       grind)
    | exact superpose eq17603 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq17603 X2 X1
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq17603 X0 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq17603 X0 X1
       grind)
    | exact resolve eq13 eq17603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17603
  have eq17899 : ∀ X0 X1 X2 : G, x = (M.op x x) ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ (k X0 y) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq17894 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17894
  have eq17908 : ∀ X0 X1 X2 X3 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ (k X3 y) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq17899 X3 X1 X2
       grind)
    | exact superpose eq17899 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq17899 X3 X1 X2
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq17899 X0 X1 X2
       grind)
    | exact resolve eq13 eq17899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17899
  have eq17913 : ∀ X0 X1 X2 X3 : G, (k X3 y) = X3 ∨ (k X1 (σ y)) = X1 ∨ (k X2 (σ x)) = X2 ∨ (k X0 x) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq17908 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17908
  have eq17962 : ∀ X0 X1 X2 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq626 y
       have i₂ := eq17913 X2 X0 X1 y
       grind)
    | exact superpose eq17913 eq626
    | (have j0 := eq626 y
       have j1 := eq17913 X2 X0 X1 x
       grind)
    | exact resolve eq626 eq17913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17913
  have eq18006 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq17962 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17962
  have eq18031 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 (σ x)) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18006 X0 X1 X2
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18006
    | (have j0 := eq18006 X0 X1 X2
       grind)
    | exact resolve eq18006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18006
  have eq18087 : ∀ X0 X1 X2 : G, (k X2 x) = X2 ∨ (k X1 (σ x)) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq18031 X0 X1 X2
       have j1 := eq13 X2 x
       grind)
    | (have r₁ := eq18031 X0 X1 X2
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq18031 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18031
  have eq18444 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 x
       have i₂ := eq18087 X1 X0 x
       grind)
    | exact superpose eq18087 eq626
    | (have j0 := eq626 x
       have j1 := eq18087 X1 X0 x
       grind)
    | exact resolve eq626 eq18087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18087
  have eq18489 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18444
  have eq18515 : ∀ X0 X1 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18489 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18489
    | (have j0 := eq18489 X0 X1
       grind)
    | exact resolve eq18489 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18489
  have eq18572 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq18515 X0 X1
       have j1 := eq13 X1 (σ y)
       grind)
    | (have r₁ := eq18515 X0 X1
       have r₂ := eq13 X0 (σ x)
       grind)
    | exact resolve eq18515 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18515
  have eq18634 : ∀ X0 X1 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1288 X0 X1
       have i₂ := eq18572 (k X0 X0) X1
       grind)
    | exact superpose eq18572 eq1288
    | (have j0 := eq1288 (σ y) X0
       have j1 := eq18572 X1 X1
       grind)
    | exact resolve eq1288 eq18572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18635 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3908 X0
       have i₂ := eq18572 (k X0 X0) x
       grind)
    | exact superpose eq18572 eq3908
    | (have j0 := eq3908 (σ y)
       have j1 := eq18572 X0 x
       grind)
    | (have r₁ := eq3908 (σ y)
       have r₂ := eq18572 X0 (σ y)
       grind)
    | (have r₁ := eq3908 (σ x)
       have r₂ := eq18572 (σ x) x
       grind)
    | exact resolve eq3908 eq18572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18572
  have eq18667 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq18635 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18635
  have eq18668 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18634
  have eq18696 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29 eq18668
    | (have j0 := eq18668 X0 X1
       grind)
    | exact resolve eq18668 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18668
  have eq18757 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq18667 (M.op X1 X1)
       grind)
    | exact superpose eq18667 eq64
    | (have j1 := eq18667 X1
       grind)
    | exact resolve eq64 eq18667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18827 : ∀ X0 X1 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1288 X0 X1
       have i₂ := eq18696 (k X0 X0) X1
       grind)
    | exact superpose eq18696 eq1288
    | (have j0 := eq1288 (σ x) X0
       have j1 := eq18696 X1 X1
       grind)
    | exact resolve eq1288 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18828 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq3908 X0
       have i₂ := eq18696 (k X0 X0) x
       grind)
    | exact superpose eq18696 eq3908
    | (have j0 := eq3908 (σ x)
       have j1 := eq18696 X0 x
       grind)
    | (have r₁ := eq3908 (σ x)
       have r₂ := eq18696 X0 (σ x)
       grind)
    | (have r₁ := eq3908 y
       have r₂ := eq18696 y x
       grind)
    | exact resolve eq3908 eq18696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18696
  have eq18860 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq18828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18828
  have eq18861 : ∀ X0 X1 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq18827 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18827
  have eq18889 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | exact superpose eq28 eq18861
    | (have j0 := eq18861 X0 X1
       grind)
    | exact resolve eq18861 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18861
  have eq19568 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq18860 (M.op X1 X1)
       grind)
    | exact superpose eq18860 eq64
    | (have j1 := eq18860 X1
       grind)
    | exact resolve eq64 eq18860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19633 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq3908 y
       have i₂ := eq18889 X0 y
       grind)
    | exact superpose eq18889 eq3908
    | (have j0 := eq3908 y
       have j1 := eq18889 X0 x
       grind)
    | (have r₁ := eq3908 y
       have r₂ := eq18889 X0 y
       grind)
    | (have r₁ := eq3908 x
       have r₂ := eq18889 x x
       grind)
    | exact resolve eq3908 eq18889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18889
  have eq19666 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq19633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19633
  have eq19761 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 y
       have i₂ := eq19666 X1
       grind)
    | exact superpose eq19666 eq64
    | (have j1 := eq19666 X1
       grind)
    | exact resolve eq64 eq19666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19666
  have eq25180 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (τ (M.op X0 (σ y))) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16993
       have i₂ := eq18757 X0 (M.op sF0 y)
       grind)
    | exact superpose eq18757 eq16993
    | (have j1 := eq18757 X0 X1
       grind)
    | exact resolve eq16993 eq18757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18757
  have eq147079 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (τ (M.op X0 (σ x))) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16993
       have i₂ := eq19568 X0 (M.op sF0 y)
       grind)
    | exact superpose eq19568 eq16993
    | (have j1 := eq19568 X0 X1
       grind)
    | exact resolve eq16993 eq19568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19568
  have eq154603 : ∀ X0 X1 : G, (M.op X0 y) = (σ (M.op X0 y)) ∨ (k X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16941
       have i₂ := eq19761 sF0 X1
       grind)
    | (have i₁ := eq16941
       have i₂ := eq19761 X0 (M.op sF0 y)
       grind)
    | exact superpose eq19761 eq16941
    | (have j1 := eq19761 X0 X1
       grind)
    | exact resolve eq16941 eq19761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19761
  have eq368882 : ∀ X0 X1 : G, (σ y) = (τ (σ y)) ∨ (k X0 (σ x)) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25180 X0 X1
       have i₂ := eq18667 (M.op X0 sF3)
       grind)
    | exact superpose eq18667 eq25180
    | (have j0 := eq25180 X0 X0
       have j1 := eq18667 X0
       grind)
    | exact resolve eq25180 eq18667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18667 eq25180
  have eq369285 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 (σ x)) = X0 ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq29 eq368882
    | (have j0 := eq368882 X1 X1
       grind)
    | exact resolve eq368882 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq368882
  have eq374291 : ∀ X0 X1 : G, (σ x) = (τ (σ x)) ∨ (k X0 y) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147079 X0 X1
       have i₂ := eq18860 (M.op X0 sF2)
       grind)
    | exact superpose eq18860 eq147079
    | (have j0 := eq147079 X0 X0
       have j1 := eq18860 X0
       grind)
    | exact resolve eq147079 eq18860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860 eq147079
  have eq374709 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 y) = X0 ∨ x = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq28 eq374291
    | (have j0 := eq374291 X1 X1
       grind)
    | exact resolve eq374291 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374291
  have eq377823 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (σ x)) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq369285 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369285
  have eq377824 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq377823 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377823
  have eq378393 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq377824 eq1288
    | (have j0 := eq1288 (σ x) X0
       grind)
    | exact resolve eq1288 eq377824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq378395 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq377824 eq3908
    | (have j0 := eq3908 (σ x)
       grind)
    | (have r₁ := eq3908 (σ x)
       have r₂ := eq377824 (σ x)
       grind)
    | exact resolve eq3908 eq377824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377824
  have eq378664 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by grind
  clear eq378395
  have eq378666 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq378393 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378393
  have eq378875 : ∀ X0 : G, (k X0 x) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq28 eq378666
    | exact resolve eq378666 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378666
  have eq379155 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq378664 eq64
    | exact resolve eq64 eq378664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379334 : x ≠ x ∨ x = (M.op x x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq3908 x
       have i₂ := eq378875 x
       grind)
    | exact superpose eq378875 eq3908
    | (have j0 := eq3908 x
       grind)
    | (have r₁ := eq3908 x
       have r₂ := eq378875 x
       grind)
    | exact resolve eq3908 eq378875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378875
  have eq379603 : x = (M.op x x) ∨ y = (σ y) := by grind
  clear eq379334
  have eq380264 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq379603
       grind)
    | exact superpose eq379603 eq64
    | exact resolve eq64 eq379603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385507 : (σ x) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq379155 eq378664
    | exact resolve eq378664 eq379155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378664
  have eq385512 : (σ x) = (M.op (M.op x y) y) ∨ y = (σ y) := by grind
  clear eq385507
  have eq385565 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq385512 eq221
    | exact resolve eq221 eq385512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq385598 : (σ x) = (τ (σ x)) ∨ y = (σ y) := by
    first
    | exact superpose eq385512 eq16993
    | exact resolve eq16993 eq385512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385512
  have eq385640 : y = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq385598
    | exact resolve eq385598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385598
  have eq385652 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq385565
    | exact resolve eq385565 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385565
  have eq385656 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = (σ x) := by
    first
    | exact superpose eq385640 eq26
    | exact resolve eq26 eq385640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385640
  have eq385914 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | exact superpose eq385652 eq219
    | exact resolve eq219 eq385652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq385652
  have eq386254 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq385914
    | exact resolve eq385914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385914
  have eq406608 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (σ x)) ∨ y = (σ y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq380264 eq379155
    | exact resolve eq379155 eq380264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379155 eq380264
  have eq406676 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (σ x)) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq406608 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406608
  have eq413189 : ∀ X0 : G, x = (M.op X0 (σ x)) ∨ y = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq379603
       have i₂ := eq406676 x X0
       grind)
    | exact superpose eq406676 eq379603
    | exact resolve eq379603 eq406676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379603 eq406676
  have eq413325 : ∀ X0 : G, x = (M.op X0 (σ x)) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq413189 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413189
  have eq413401 : x = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | exact superpose eq468 eq413325
    | exact resolve eq413325 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413325
  have eq413677 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq413401 eq14
    | exact resolve eq14 eq413401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413401
  have eq413686 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ y = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq413677 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq413677
    | (have j0 := eq413677 X0 X1
       grind)
    | exact resolve eq413677 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413677
  have eq413705 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq413686 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq413686
    | exact resolve eq413686 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413686
  have eq414785 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq413705 eq16941
    | exact resolve eq16941 eq413705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414816 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq413705 eq386254
    | exact resolve eq386254 eq413705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386254 eq413705
  have eq414825 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq414816
  have eq414835 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq414785
    | exact resolve eq414785 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414785
  have eq414853 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq414825 eq27
    | exact resolve eq27 eq414825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414825
  have eq415849 : y = (σ y) := by
    first
    | (have r₁ := eq414853
       have r₂ := eq414835
       grind)
    | exact resolve eq414853 eq414835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414835 eq414853
  have eq801505 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq154603 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq154603
    | (have j0 := eq154603 x X0
       grind)
    | exact resolve eq154603 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154603
  have eq801966 : ∀ X0 : G, (k X0 x) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq801505
    | (have j0 := eq801505 X0
       grind)
    | exact resolve eq801505 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801505
  have eq803435 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq626 x
       have i₂ := eq801966 x
       grind)
    | exact superpose eq801966 eq626
    | (have j0 := eq626 x
       grind)
    | exact resolve eq626 eq801966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq803445 : x ≠ x ∨ x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq3908 x
       have i₂ := eq801966 x
       grind)
    | exact superpose eq801966 eq3908
    | (have j0 := eq3908 x
       grind)
    | (have r₁ := eq3908 x
       have r₂ := eq801966 x
       grind)
    | exact resolve eq3908 eq801966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801966
  have eq803837 : x = (M.op x x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq803445
  have eq803844 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq803435
  have eq804141 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq803844
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq803844
    | exact resolve eq803844 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq803844
  have eq804913 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq803837
       grind)
    | exact superpose eq803837 eq64
    | exact resolve eq64 eq803837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807616 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq804141 eq64
    | exact resolve eq64 eq804141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831224 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq804913 eq804913
    | exact resolve eq804913 eq804913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804913
  have eq831410 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have j0 := eq831224 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831224
  have eq834551 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq807616 eq804141
    | exact resolve eq804141 eq807616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804141 eq807616
  have eq834558 : (σ x) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq834551
  have eq834817 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq834558 eq16993
    | exact resolve eq16993 eq834558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16993 eq834558
  have eq834876 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq834817
    | exact resolve eq834817 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq834817
  have eq925692 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq803837
       have i₂ := eq831410 x X0
       grind)
    | (have i₁ := eq803837
       have i₂ := eq831410 X0 x
       grind)
    | exact superpose eq831410 eq803837
    | exact resolve eq803837 eq831410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803837 eq831410
  have eq925713 : ∀ X0 : G, x = (M.op X0 x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq925692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925692
  have eq926999 : x = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq468 eq925713
    | exact resolve eq925713 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq925713
  have eq928474 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq926999 eq14
    | exact resolve eq14 eq926999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926999
  have eq928483 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq928474 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq928474
    | (have j0 := eq928474 X0 X1
       grind)
    | exact resolve eq928474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928474
  have eq928505 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq928483 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq928483
    | exact resolve eq928483 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928483
  have eq937278 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq928505 eq16941
    | exact resolve eq16941 eq928505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16941 eq928505
  have eq937341 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq937278
    | exact resolve eq937278 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq937278
  have eq937342 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq937341
  have eq1190714 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq374709 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374709
  have eq1190715 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq1190714 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190714
  have eq1195818 : y ≠ y ∨ y = (M.op y y) ∨ x = (σ x) := by
    first
    | (have i₁ := eq3908 y
       have i₂ := eq1190715 y
       grind)
    | exact superpose eq1190715 eq3908
    | (have j0 := eq3908 y
       grind)
    | (have r₁ := eq3908 y
       have r₂ := eq1190715 y
       grind)
    | exact resolve eq3908 eq1190715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908 eq1190715
  have eq1196430 : y = (M.op y y) ∨ x = (σ x) := by grind
  clear eq1195818
  have eq1200614 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ x = (σ x) := by
    intro X0
    first
    | (have i₁ := eq64 X0 y
       have i₂ := eq1196430
       grind)
    | exact superpose eq1196430 eq64
    | exact resolve eq64 eq1196430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq1196430
  have eq1202548 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | (have i₁ := eq385656
       have i₂ := eq1200614 sF2
       grind)
    | exact superpose eq1200614 eq385656
    | exact resolve eq385656 eq1200614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385656
  have eq1202557 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) := by grind
  clear eq1202548
  have eq1202834 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 y) ∨ x = (σ x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq1202557 eq1200614
    | exact resolve eq1200614 eq1202557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200614 eq1202557
  have eq1202848 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 y) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq1202834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202834
  have eq1211121 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq1202848 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1202848
    | (have j0 := eq1202848 x
       grind)
    | exact resolve eq1202848 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202848
  have eq1211534 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq1211121 eq27
    | exact resolve eq27 eq1211121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211121
  have eq1212093 : x = (σ x) := by
    first
    | (have r₁ := eq1211534
       have r₂ := eq834876
       grind)
    | exact resolve eq1211534 eq834876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834876 eq1211534
  have eq1212242 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1212093 eq26
    | exact resolve eq26 eq1212093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1212093
  have eq1213000 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq415849 eq1212242
    | exact resolve eq1212242 eq415849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415849 eq1212242
  have eq1213073 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1213000
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1213000
    | exact resolve eq1213000 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1213000
  have eq1213198 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1213073 eq27
    | exact resolve eq27 eq1213073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1213073
  have eq1213755 : False := by grind
  exact eq1213755

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_x_pxx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq51 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X2))) ≠ X0 ∨ (k X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X2 (M.op X1 X2))) (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq14 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq70 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq44
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq147 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq505 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq648
    | exact resolve eq648 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq652 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq649
       have r₂ := eq28
       grind)
    | exact resolve eq649 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq654 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq652
    | exact resolve eq652 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq668 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (k (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq61 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq670 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq654 eq52
    | (have r₁ := eq52
       have r₂ := eq654
       grind)
    | exact resolve eq52 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq672 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq670
  have eq711 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op (σ X1) (σ (k X0 X1))))) = X2 ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 X0 X1
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq732 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq672 eq100
    | exact resolve eq100 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq733 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq672 eq56
    | exact resolve eq56 eq672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq672
  have eq736 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq732
  have eq740 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq733
    | exact resolve eq733 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq743 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq740
       have r₂ := eq51
       grind)
    | exact resolve eq740 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq740
  have eq770 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq736 eq30
    | exact resolve eq30 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq736
  have eq788 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq770
    | exact resolve eq770 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq789 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq788
  have eq791 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq789 eq29
    | exact resolve eq29 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq813 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq791
    | exact resolve eq791 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq814 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq813 eq21
    | exact resolve eq21 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq817 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq813 eq57
    | exact resolve eq57 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq814
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq814
    | exact resolve eq814 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq2510 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq505 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq505
    | (have j0 := eq505 (τ X0)
       grind)
    | exact resolve eq505 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq2517 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2510 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2510
    | (have j0 := eq2510 X0
       grind)
    | exact resolve eq2510 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2530 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2517 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2517
    | (have j0 := eq2517 X0
       grind)
    | exact resolve eq2517 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq8296 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq668 X0 X1
       grind)
    | exact superpose eq668 eq505
    | (have j0 := eq505 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq505 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8299 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq8296 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq9250 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq711 x y X0
       have i₂ := eq743
       grind)
    | exact superpose eq743 eq711
    | (have j0 := eq711 x y x
       grind)
    | exact resolve eq711 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq743
  have eq9437 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9250 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9250
    | (have j0 := eq9250 X0
       grind)
    | exact resolve eq9250 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9250
  have eq9527 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9437 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9437
    | (have j0 := eq9437 X0
       grind)
    | exact resolve eq9437 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9437
  have eq9613 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9527 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9527
    | (have j0 := eq9527 X0
       grind)
    | exact resolve eq9527 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9527
  have eq9667 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9613 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9613
    | (have j0 := eq9613 X0
       grind)
    | exact resolve eq9613 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9613
  have eq9668 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq9667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9667
  have eq9717 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9668 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9668
    | (have j0 := eq9668 X0
       grind)
    | exact resolve eq9668 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9668
  have eq9757 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9717 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq9717
    | (have j0 := eq9717 X0
       grind)
    | exact resolve eq9717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9717
  have eq9773 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq9757
    | (have j0 := eq9757 X0
       grind)
    | exact resolve eq9757 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9757
  have eq953278 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq9773 eq668
    | exact resolve eq668 eq9773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq9773
  have eq955373 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq835 eq953278
    | exact resolve eq953278 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835 eq953278
  have eq955568 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq955373
  have eq955577 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq955568
       have r₂ := eq28
       grind)
    | exact resolve eq955568 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955568
  have eq956203 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq955577 eq147
    | exact resolve eq147 eq955577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq955577
  have eq956289 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq956203
    | exact resolve eq956203 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956203
  have eq956492 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq956289 eq2530
    | (have j0 := eq2530 (M.op x y)
       grind)
    | (have r₁ := eq2530 (M.op x y)
       have r₂ := eq956289
       grind)
    | exact resolve eq2530 eq956289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530 eq956289
  have eq956516 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq956492
  have eq956909 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq813 eq956516
    | exact resolve eq956516 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956516
  have eq956933 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq956909
  have eq979432 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq817 X0
       have i₂ := eq956933
       grind)
    | exact superpose eq956933 eq817
    | exact resolve eq817 eq956933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq956933
  have eq979457 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq979432 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979432
  have eq979458 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq979457 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq979457
    | (have j0 := eq979457 X0
       grind)
    | exact resolve eq979457 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979457
  have eq993971 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq813 eq979458
    | exact resolve eq979458 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq979458
  have eq994295 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq993971 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993971
  have eq995434 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq994295 x
       grind)
    | exact superpose eq994295 eq19
    | (have j1 := eq994295 x
       grind)
    | exact resolve eq19 eq994295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994295
  have eq995441 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq995434
  have eq995673 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq995441 eq29
    | exact resolve eq29 eq995441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995441
  have eq996708 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq995673
    | exact resolve eq995673 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq995673
  have eq996709 : x = (M.op x y) ∨ x = y := by grind
  clear eq996708
  have eq996711 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq996709 eq21
    | exact resolve eq21 eq996709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996714 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq996709 eq57
    | exact resolve eq57 eq996709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq996709
  have eq997472 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq996711
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq996711
    | exact resolve eq996711 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996711
  have eq997476 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq997472 eq27
    | exact resolve eq27 eq997472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997472
  have eq1033248 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq8299 y x
       have i₂ := eq996714 y
       grind)
    | exact superpose eq996714 eq8299
    | exact resolve eq8299 eq996714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8299 eq996714
  have eq1033691 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1033248
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1033248
    | exact resolve eq1033248 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033248
  have eq1036134 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq1033691 eq14
    | exact resolve eq14 eq1033691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033691
  have eq1201737 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f1201737_14 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 ∨ y = x := by
      intro X0
      grind
    have f1201737_20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1201737_23 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f1201737_24 : y ≠ x := by grind
    have f1201737_26 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
      intro X0
      first
      | (have j0 := f1201737_14 X0
         grind)
      | (have r₁ := f1201737_14 X0
         have r₂ := f1201737_24
         grind)
      | exact resolve f1201737_14 f1201737_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1201737_50 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1201737_20 X0 (σ y) (σ y)
         have i₂ := f1201737_26 (σ y)
         grind)
      | exact superpose f1201737_26 f1201737_20
      | exact resolve f1201737_20 f1201737_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1201737_54 : X0 ≠ X0 := by
      first
      | (have i₁ := f1201737_23
         have i₂ := f1201737_50 X0
         grind)
      | exact superpose f1201737_50 f1201737_23
      | (have r₁ := f1201737_23
         have r₂ := f1201737_50 X0
         grind)
      | exact resolve f1201737_23 f1201737_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1201737_59 : False := by grind
    exact f1201737_59
  clear eq1036134
  have eq1204203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1201737 eq997476
    | exact resolve eq997476 eq1201737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997476 eq1201737
  have eq1204211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1204203
  have eq1204249 : x = y := by
    first
    | (have r₁ := eq1204211
       have r₂ := eq28
       grind)
    | exact resolve eq1204211 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204211
  have eq1204433 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1204249
       grind)
    | exact superpose eq1204249 eq19
    | exact resolve eq19 eq1204249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1204434 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1204249
       grind)
    | exact superpose eq1204249 eq25
    | exact resolve eq25 eq1204249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1204249
  have eq1204830 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1204434
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1204434
    | exact resolve eq1204434 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204434
  have eq1206711 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1204830 eq27
    | exact resolve eq27 eq1204830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1207608 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq1204433
       grind)
    | exact superpose eq1204433 eq70
    | exact resolve eq70 eq1204433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1207613 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq1204433
       grind)
    | exact superpose eq1204433 eq13
    | (have j0 := eq13 x x
       grind)
    | exact resolve eq13 eq1204433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204433
  have eq1207641 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq1207608
    | exact resolve eq1207608 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207608
  have eq1207780 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  have eq1207829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1206711 eq1207780
    | exact resolve eq1207780 eq1206711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207780
  have eq1207840 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1207829
       have r₂ := eq28
       grind)
    | exact resolve eq1207829 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207829
  have eq1207842 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1206711 eq1207840
    | exact resolve eq1207840 eq1206711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207840
  have eq1213889 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1207842 eq28
    | exact resolve eq28 eq1207842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213890 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1207842 eq52
    | exact resolve eq52 eq1207842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1207842
  have eq1214041 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1213890
       have r₂ := eq1204830
       grind)
    | exact resolve eq1213890 eq1204830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213890
  have eq1214065 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1204830 eq1214041
    | exact resolve eq1214041 eq1204830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204830 eq1214041
  have eq1220462 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1214065 eq50
    | exact resolve eq50 eq1214065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1220492 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1214065 eq1207641
    | exact resolve eq1207641 eq1214065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207641 eq1214065
  have eq1220576 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1220492
  have eq1220594 : x = (M.op x y) := by
    first
    | (have r₁ := eq1220576
       have r₂ := eq1213889
       grind)
    | exact resolve eq1220576 eq1213889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213889 eq1220576
  have eq1220601 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1220462
    | exact resolve eq1220462 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1220462
  have eq1220614 : x = (k x x) := by
    first
    | (have r₁ := eq1220601
       have r₂ := eq1207613
       grind)
    | exact resolve eq1220601 eq1207613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207613 eq1220601
  have eq1226781 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1220594 eq21
    | exact resolve eq21 eq1220594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1220594
  have eq1227600 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1226781
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1226781
    | exact resolve eq1226781 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226781
  have eq1237589 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq505 x
       have i₂ := eq1220614
       grind)
    | exact superpose eq1220614 eq505
    | (have j0 := eq505 x
       grind)
    | exact resolve eq505 eq1220614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505 eq1220614
  have eq1237625 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1237589
  have eq1237666 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1237625
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1237625
    | exact resolve eq1237625 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1237625
  have eq1237725 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1206711 eq1237666
    | exact resolve eq1237666 eq1206711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206711 eq1237666
  have eq1237780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1227600 eq1237725
    | exact resolve eq1237725 eq1227600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227600 eq1237725
  have eq1237829 : False := by grind
  exact eq1237829

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pxy_y_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq33 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op X2 (M.op X1 X2))) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 (M.op X1 X2))) X0) = (M.op (M.op X1 (M.op X2 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq33 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq196 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq88 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq12 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq88 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq201 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq209 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq201 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq34 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq34 eq201
    | (have j0 := eq201 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact resolve eq201 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq218 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ≠ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 X1
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq209
    | (have j0 := eq209 X0 X1
       grind)
    | exact resolve eq209 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq219 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq218 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq1815 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (τ X0) (τ X1)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq205
    | (have j0 := eq205 (τ X0) (τ X1)
       grind)
    | exact resolve eq205 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq205
  have eq1845 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1815 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1815
    | (have j0 := eq1815 X0 X1
       grind)
    | exact resolve eq1815 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1861 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op (σ (τ X1)) (σ (τ X0))) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1845 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1845
    | (have j0 := eq1845 X0 X1
       grind)
    | exact resolve eq1845 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1845
  have eq1874 : ∀ X0 X1 : G, (M.op (σ (τ X1)) (σ (τ X0))) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1861 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq1861
    | (have j0 := eq1861 X0 X1
       grind)
    | exact resolve eq1861 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1886 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 (σ (τ X0))) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1874 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1874
    | (have j0 := eq1874 X0 X1
       grind)
    | exact resolve eq1874 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1898 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1886 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1886
    | (have j0 := eq1886 X0 X1
       grind)
    | exact resolve eq1886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1905 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1898 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1898
    | (have j0 := eq1898 X0 X1
       grind)
    | exact resolve eq1898 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1912 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1905 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1905
    | (have j0 := eq1905 X0 X1
       grind)
    | exact resolve eq1905 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1905
  have eq1915 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1912 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1912
    | (have j0 := eq1912 X0 X1
       grind)
    | exact resolve eq1912 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1912
  have eq3287 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq93 X0 X1
       grind)
    | exact superpose eq93 eq12
    | (have j1 := eq93 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq12 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq3307 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3287
  have eq5091 : ∀ X0 X1 X2 : G, (k (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) X2) = (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))
       have i₂ := eq219 X0 X1
       grind)
    | exact superpose eq219 eq34
    | exact resolve eq34 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5112 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) X2) = (k (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5091 X0 X1 X2
       have i₂ := eq219 X0 X1
       grind)
    | exact superpose eq219 eq5091
    | exact resolve eq5091 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq5129 : ∀ X0 X1 X2 : G, (k (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5112 X0 X1 X2
       have i₂ := eq219 X0 X1
       grind)
    | exact superpose eq219 eq5112
    | exact resolve eq5112 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq5112
  have eq218215 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq3307 X0 X1
       grind)
    | exact superpose eq3307 eq11
    | (have j1 := eq3307 X0 X1
       grind)
    | exact resolve eq11 eq3307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq218449 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 X0) = X0 ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq218215 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq218215
    | (have j0 := eq218215 X0 X1
       grind)
    | exact resolve eq218215 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq218215
  have eq218492 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218449 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq218449 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq218449 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218449
  have eq218675 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1915 X0 X0
       have i₂ := eq218492 X0 X1
       grind)
    | exact superpose eq218492 eq1915
    | (have j0 := eq1915 X0 X0
       have j1 := eq218492 X0 X1
       grind)
    | (have r₁ := eq1915 X0 X0
       have r₂ := eq218492 X0 X1
       grind)
    | exact resolve eq1915 eq218492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1915
  have eq218800 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq218492 (σ X0) X1
       grind)
    | exact superpose eq218492 eq30
    | (have j1 := eq218492 (σ X0) X1
       grind)
    | exact resolve eq30 eq218492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq218492
  have eq218919 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq218675 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218675
  have eq218920 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq218919 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218919
  have eq219024 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq218800 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq218800
    | (have j0 := eq218800 X0 X1
       grind)
    | exact resolve eq218800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218800
  have eq219186 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219024 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq219024
    | (have j0 := eq219024 X0 X1
       grind)
    | exact resolve eq219024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219024
  have eq220575 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq218920 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq218920
    | (have j0 := eq218920 X1 X1
       grind)
    | exact resolve eq218920 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218920
  have eq221438 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq220575 (τ X1) X0
       grind)
    | exact superpose eq220575 eq18
    | (have j1 := eq220575 X0 X0
       grind)
    | exact resolve eq18 eq220575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq222807 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220575 X0 X0
       have i₂ := eq219186 X0 X1
       grind)
    | exact superpose eq219186 eq220575
    | (have j0 := eq220575 X0 X0
       have j1 := eq219186 X0 X1
       grind)
    | exact resolve eq220575 eq219186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219186 eq220575
  have eq223047 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq222807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222807
  have eq225481 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq221438 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq221438
    | (have j0 := eq221438 X1 X1
       grind)
    | exact resolve eq221438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221438
  have eq225788 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq225481 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq225481
    | (have j0 := eq225481 X0 X1
       grind)
    | exact resolve eq225481 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225481
  have eq227159 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq223047 x y
       grind)
    | exact superpose eq223047 eq16
    | (have j1 := eq223047 x x
       grind)
    | exact resolve eq16 eq223047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223047
  have eq227417 : x = (M.op x x) := by
    first
    | (have j1 := eq225788 x x
       grind)
    | (have r₁ := eq227159
       have r₂ := eq225788 y x
       grind)
    | exact resolve eq227159 eq225788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225788 eq227159
  have eq227850 : ∀ X0 : G, (k (M.op x (M.op x x)) X0) = (M.op (M.op x (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0 x x
       have i₂ := eq227417
       grind)
    | exact superpose eq227417 eq34
    | exact resolve eq34 eq227417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq227898 : ∀ X0 : G, (k (σ (M.op x (M.op x x))) X0) = (M.op (σ (M.op x (M.op x x))) X0) := by
    intro X0
    first
    | (have i₁ := eq5129 x x x
       have i₂ := eq227417
       grind)
    | exact superpose eq227417 eq5129
    | exact resolve eq5129 eq227417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5129
  have eq227994 : ∀ X0 : G, (k (σ (M.op x x)) X0) = (M.op (σ (M.op x x)) X0) := by
    intro X0
    first
    | (have i₁ := eq227898 X0
       have i₂ := eq227417
       grind)
    | exact superpose eq227417 eq227898
    | exact resolve eq227898 eq227417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227898
  have eq228042 : ∀ X0 : G, (M.op (M.op x x) X0) = (k (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq227850 X0
       have i₂ := eq227417
       grind)
    | exact superpose eq227417 eq227850
    | exact resolve eq227850 eq227417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227850
  have eq228090 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq227994 X0
       have i₂ := eq227417
       grind)
    | exact superpose eq227417 eq227994
    | exact resolve eq227994 eq227417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227994
  have eq228138 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq228042 X0
       have i₂ := eq227417
       grind)
    | exact superpose eq227417 eq228042
    | exact resolve eq228042 eq227417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227417 eq228042
  have eq236168 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq228090 (σ X0)
       grind)
    | exact superpose eq228090 eq15
    | exact resolve eq15 eq228090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228090
  have eq236457 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq236168 X0
       have i₂ := eq228138 X0
       grind)
    | exact superpose eq228138 eq236168
    | exact resolve eq236168 eq228138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228138 eq236168
  have eq247476 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq236457 y
       grind)
    | exact superpose eq236457 eq16
    | (have r₁ := eq16
       have r₂ := eq236457 y
       grind)
    | exact resolve eq16 eq236457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236457
  have eq247749 : False := by grind
  exact eq247749

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq270 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq88 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq273 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq274 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq276 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq280 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq276 X0 X1
       have j1 := eq272 X0 X1
       grind)
    | (have r₁ := eq276 X0 X1
       have r₂ := eq272 X0 X1
       grind)
    | (have r₁ := eq276 (k X0 X1) X0
       have r₂ := eq272 X0 X1
       grind)
    | (have r₁ := eq276 X0 X0
       have r₂ := eq272 X0 X0
       grind)
    | exact resolve eq276 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq276
  have eq601 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq280 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq280
    | exact resolve eq280 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq280 x y
       grind)
    | exact superpose eq280 eq16
    | (have j1 := eq280 x y
       grind)
    | exact resolve eq16 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq624 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq601
    | (have j0 := eq601 X0 X1
       grind)
    | exact resolve eq601 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq601
  have eq626 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq624 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq624
    | exact resolve eq624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq689 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq626 (τ X0) X1
       grind)
    | exact superpose eq626 eq18
    | (have j1 := eq626 (τ X0) X1
       grind)
    | exact resolve eq18 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq626
  have eq958 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq689 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq689
    | exact resolve eq689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq1011 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq958 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq958
    | (have j0 := eq958 X0 X1
       grind)
    | exact resolve eq958 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958
  have eq1121 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq609
       have i₂ := eq1011 x y
       grind)
    | exact superpose eq1011 eq609
    | (have j1 := eq1011 (σ x) (σ y)
       grind)
    | (have r₁ := eq609
       have r₂ := eq1011 x y
       grind)
    | exact resolve eq609 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1121
  have eq1187 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1122
  have eq1196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq609
       have i₂ := eq1187
       grind)
    | exact superpose eq1187 eq609
    | exact resolve eq609 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq1187
  have eq1197 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1196
  have eq1198 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1197
  have eq1211 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1198
  have eq1221 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1211
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1211
    | exact resolve eq1211 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1211
  have eq1227 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1221
       grind)
    | exact superpose eq1221 eq16
    | exact resolve eq16 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1280 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1227
       have i₂ := eq1011 x y
       grind)
    | exact superpose eq1011 eq1227
    | (have j1 := eq1011 x y
       grind)
    | (have r₁ := eq1227
       have r₂ := eq1011 x y
       grind)
    | exact resolve eq1227 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1281 : x = (M.op y y) := by grind
  clear eq1280
  have eq1287 : (M.op x y) = (k x y) := by grind
  clear eq1281
  have eq1343 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1227
       have i₂ := eq1287
       grind)
    | exact superpose eq1287 eq1227
    | exact resolve eq1227 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq1287
  have eq1346 : False := by grind
  exact eq1346

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pxy_pyx_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
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
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact superpose eq13 eq15
    | (have j1 := eq13 (σ X0) (σ X1)
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
  clear eq33
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
  have eq208 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq944 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq208 x y
       grind)
    | exact superpose eq208 eq16
    | (have j1 := eq208 y y
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
  have eq977 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ X0)))) = X1 ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq955 X0
       grind)
    | exact superpose eq955 eq9
    | (have j1 := eq955 X0
       grind)
    | exact resolve eq9 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq984 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ X0))) = X1 ∨ (σ X0) ≠ (σ (k X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq955 eq977
    | (have j0 := eq977 X0 X1
       have j1 := eq955 X0
       grind)
    | exact resolve eq977 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq989 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq955 eq984
    | (have j0 := eq984 X0 X1
       have j1 := eq955 X0
       grind)
    | exact resolve eq984 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955 eq984
  have eq1795 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq989
    | (have j0 := eq989 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq989 X0 (σ X0)
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq989 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ X0)) ∨ (M.op X1 (σ (τ X0))) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 (τ X0) X1
       have i₂ := eq57 (τ X0) X0
       grind)
    | exact superpose eq57 eq989
    | (have j0 := eq989 (τ X0) X1
       have j1 := eq57 X0 X0
       grind)
    | (have r₁ := eq989 X0 (σ X0)
       have r₂ := eq57 X0 (σ X0)
       grind)
    | exact resolve eq989 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1809 : ∀ X0 X1 : G, (σ (τ (τ X0))) ≠ (σ (τ (τ X0))) ∨ (M.op X1 (σ (τ (τ X0)))) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq989 (τ (τ X0)) X1
       have i₂ := eq107 (τ (τ X0)) X0
       grind)
    | exact superpose eq107 eq989
    | (have j0 := eq989 (τ (τ X0)) X1
       have j1 := eq107 X0 X0
       grind)
    | (have r₁ := eq989 X0 (σ X0)
       have r₂ := eq107 X0 (σ X0)
       grind)
    | exact resolve eq989 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq989
  have eq1828 : ∀ X0 X1 : G, (M.op X1 (σ (τ (τ X0)))) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq1809 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq1830 : ∀ X0 X1 : G, (M.op X1 (σ (τ X0))) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq1807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1842 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have j0 := eq1795 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1853 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1828 X0 X1
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq1828
    | (have j0 := eq1828 X0 X1
       grind)
    | exact resolve eq1828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq1855 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1830 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1830
    | (have j0 := eq1830 X0 X1
       grind)
    | exact resolve eq1830 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1935 : (σ (M.op x y)) ≠ (σ x) ∨ y ≠ (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1842 y (σ x)
       grind)
    | exact superpose eq1842 eq16
    | (have j1 := eq1842 y x
       grind)
    | exact resolve eq16 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1951 : (σ x) ≠ (σ x) ∨ y ≠ (M.op y y) := by
    first
    | exact superpose eq1855 eq1935
    | (have j1 := eq1855 y x
       grind)
    | (have r₁ := eq1935
       have r₂ := eq1855 y y
       grind)
    | exact resolve eq1935 eq1855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855 eq1935
  have eq1952 : y ≠ (M.op y y) := by grind
  clear eq1951
  have eq2028 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1853 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1853
    | (have j0 := eq1853 (σ X0) X1
       grind)
    | exact resolve eq1853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq5648 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq573
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq573
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq573
       have r₂ := eq13 x (σ x)
       grind)
    | (have r₁ := eq573
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq573 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq5651 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x ≠ (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq5648
  have eq5654 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2028 x x
       grind)
    | (have r₁ := eq5651
       have r₂ := eq2028 (σ x) (σ x)
       grind)
    | (have r₁ := eq5651
       have r₂ := eq2028 y x
       grind)
    | (have r₁ := eq5651
       have r₂ := eq2028 x x
       grind)
    | exact resolve eq5651 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651
  have eq5656 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2028 x x
       grind)
    | (have r₁ := eq5654
       have r₂ := eq2028 (σ x) (σ x)
       grind)
    | (have r₁ := eq5654
       have r₂ := eq2028 y x
       grind)
    | exact resolve eq5654 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5654
  have eq5657 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq5656
       have r₂ := eq1952
       grind)
    | exact resolve eq5656 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq6207 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq944
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq944
    | (have j1 := eq14 (σ y) (σ y)
       grind)
    | exact resolve eq944 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq6211 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq6207
  have eq6212 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq1842 y (σ y)
       grind)
    | (have r₁ := eq6211
       have r₂ := eq1842 (σ y) x
       grind)
    | (have r₁ := eq6211
       have r₂ := eq1842 (σ x) x
       grind)
    | (have r₁ := eq6211
       have r₂ := eq1842 y x
       grind)
    | exact resolve eq6211 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211
  have eq6213 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq1842 y (σ y)
       grind)
    | (have r₁ := eq6212
       have r₂ := eq1842 (σ y) x
       grind)
    | (have r₁ := eq6212
       have r₂ := eq1842 (σ x) x
       grind)
    | (have r₁ := eq6212
       have r₂ := eq1842 x x
       grind)
    | exact resolve eq6212 eq1842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842 eq6212
  have eq6214 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq6213
       have r₂ := eq5657
       grind)
    | exact resolve eq6213 eq5657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5657 eq6213
  have eq6228 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2028 y X0
       have i₂ := eq6214
       grind)
    | exact superpose eq6214 eq2028
    | (have j0 := eq2028 y X0
       grind)
    | (have r₁ := eq2028 y x
       have r₂ := eq6214
       grind)
    | exact resolve eq2028 eq6214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028 eq6214
  have eq6272 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq6228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6228
  have eq6301 : y ≠ y := by
    first
    | (have i₁ := eq1952
       have i₂ := eq6272 y
       grind)
    | exact superpose eq6272 eq1952
    | (have r₁ := eq1952
       have r₂ := eq6272 y
       grind)
    | exact resolve eq1952 eq6272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1952 eq6272
  have eq6302 : False := by grind
  exact eq6302

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pyy_pyx_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  clear eq24
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq74 y x
       grind)
    | exact superpose eq74 eq71
    | (have j1 := eq74 y x
       grind)
    | exact resolve eq71 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq107
    | exact resolve eq107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq574 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq108 eq74
    | (have j0 := eq74 (σ y) (σ x)
       grind)
    | exact resolve eq74 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq574
    | exact resolve eq574 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq578 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq575
       have r₂ := eq27
       grind)
    | exact resolve eq575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq582 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq578 eq14
    | exact resolve eq14 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq584 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq582
    | (have j0 := eq582 X0
       grind)
    | exact resolve eq582 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq593 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq584 eq51
    | exact resolve eq51 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq584
  have eq656 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq593 X1
       grind)
    | exact superpose eq593 eq14
    | (have j1 := eq593 X1
       grind)
    | exact resolve eq14 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq658 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq656 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq656
    | (have j0 := eq656 X0 X1
       grind)
    | exact resolve eq656 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq667 : ∀ X0 X1 : G, (M.op X1 (σ x)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0
       have i₂ := eq658 X0 (M.op x (M.op y sF0))
       grind)
    | exact superpose eq658 eq50
    | (have j1 := eq658 X0 X1
       grind)
    | exact resolve eq50 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq671 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq667 (M.op X1 X1) X1
       grind)
    | exact superpose eq667 eq13
    | (have j0 := eq13 X0 (σ x)
       have j1 := eq667 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq667 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq667 x X1
       grind)
    | exact resolve eq13 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq677 : ∀ X0 X1 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq671 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq684 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq108
       have i₂ := eq677 X0 (k sF3 sF2)
       grind)
    | exact superpose eq677 eq108
    | (have j1 := eq677 X0 y
       grind)
    | exact resolve eq108 eq677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq677
  have eq690 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq684
    | (have j0 := eq684 y
       grind)
    | exact resolve eq684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq692 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq690 y
       grind)
    | (have r₁ := eq690 X0
       have r₂ := eq27
       grind)
    | exact resolve eq690 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq697 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq692 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq698 : y = (M.op y x) := by grind
  clear eq697
  have eq704 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq698
       grind)
    | exact superpose eq698 eq14
    | exact resolve eq14 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq706 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq704 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq704
    | (have j0 := eq704 X0
       grind)
    | exact resolve eq704 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq743 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq706 eq50
    | exact resolve eq50 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq706
  have eq747 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq743 x
       grind)
    | exact superpose eq743 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq743 x
       grind)
    | exact resolve eq13 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq747 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq758 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq754 x
       grind)
    | exact superpose eq754 eq43
    | exact resolve eq43 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq759 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq754 y
       grind)
    | exact superpose eq754 eq71
    | exact resolve eq71 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq754
  have eq764 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq759
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq759
    | exact resolve eq759 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq759
  have eq765 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq758
       have i₂ := eq743 x
       grind)
    | exact superpose eq743 eq758
    | exact resolve eq758 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq758
  have eq766 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq764
    | exact resolve eq764 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq764
  have eq767 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq765
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq765
    | exact resolve eq765 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq765
  have eq784 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq767 eq74
    | (have j0 := eq74 (σ x) (σ x)
       grind)
    | exact resolve eq74 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq767
  have eq785 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq784
  have eq840 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq785 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq785
       grind)
    | exact resolve eq13 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq844 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq840 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq844 eq766
    | exact resolve eq766 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq844
  have eq946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq939
    | exact resolve eq939 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq939
  have eq954 : False := by grind
  exact eq954

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have r₂ := eq9 (M.op X1 (M.op X2 (M.op X1 X2))) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq34 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
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
  have eq75 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq36
  have eq82 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op X1 (M.op X2 (M.op X1 X2)))
       have i₂ := eq35 X1 X2 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq35
  have eq86 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (M.op X1 X2))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq82 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq107 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) ∨ (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    grind
  clear eq86
  have eq109 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq252 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq252
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq252
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq252
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq252
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq252 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq1991 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq1990
  have eq3650 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq75 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq75 X0
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3674 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq3675 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3650 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3650
  have eq3780 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3675 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3675
    | exact resolve eq3675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675
  have eq3824 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3780 X0 X1
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq3780
    | (have j0 := eq3780 X0 X1
       grind)
    | exact resolve eq3780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3780
  have eq3828 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3824 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3824
    | (have j0 := eq3824 X0 X1
       grind)
    | exact resolve eq3824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq4787 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq3674 (σ X0)
       have i₂ := eq29 X0 (σ X0)
       grind)
    | exact superpose eq29 eq3674
    | exact resolve eq3674 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3674
  have eq4818 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (τ (σ X0))) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4787 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4787
    | (have j0 := eq4787 X0
       grind)
    | exact resolve eq4787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4787
  have eq4835 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq4818 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4818
    | (have j0 := eq4818 X0
       grind)
    | exact resolve eq4818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4818
  have eq4842 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4835 X0
       have j1 := eq3828 X0 x
       grind)
    | (have r₁ := eq4835 X0
       have r₂ := eq3828 X0 X0
       grind)
    | exact resolve eq4835 eq3828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828 eq4835
  have eq4932 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq4842 (σ X0)
       grind)
    | exact superpose eq4842 eq15
    | exact resolve eq15 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4952 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4932 X0
       have i₂ := eq4842 X0
       grind)
    | exact superpose eq4842 eq4932
    | exact resolve eq4932 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842 eq4932
  have eq5487 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq4952 X0
       grind)
    | exact superpose eq4952 eq9
    | exact resolve eq9 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7618 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5487 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq9 eq5487
    | exact resolve eq5487 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5487
  have eq7766 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7618 X0 X1 X2
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq7618
    | exact resolve eq7618 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7618
  have eq7806 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7766 X0 X1 X2
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq7766
    | exact resolve eq7766 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq7766
  have eq14669 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1991
       grind)
    | exact superpose eq1991 eq16
    | exact resolve eq16 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq14670 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq14669
       have r₂ := eq4952 x
       grind)
    | exact resolve eq14669 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14669
  have eq14671 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq14670
       have i₂ := eq4952 y
       grind)
    | exact superpose eq4952 eq14670
    | exact resolve eq14670 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14670
  have eq22304 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq14671
       grind)
    | exact superpose eq14671 eq10
    | exact resolve eq10 eq14671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14671
  have eq22394 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22304
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22304
    | exact resolve eq22304 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22304
  have eq22416 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22394
       grind)
    | exact superpose eq22394 eq16
    | exact resolve eq16 eq22394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22394
  have eq22417 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq22416
       have r₂ := eq4952 x
       grind)
    | exact resolve eq22416 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952 eq22416
  have eq22855 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq22417
       grind)
    | exact superpose eq22417 eq10
    | exact resolve eq10 eq22417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22417
  have eq22952 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq22855
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22855
    | exact resolve eq22855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22855
  have eq22953 : y = (M.op y y) := by grind
  clear eq22952
  have eq23003 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y y
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq9
    | exact resolve eq9 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23035 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7806 y y X0
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq7806
    | exact resolve eq7806 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7806
  have eq23059 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23035 X0
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq23035
    | exact resolve eq23035 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23035
  have eq23091 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23003 X0
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq23003
    | exact resolve eq23003 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23003
  have eq23122 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23059 X0
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq23059
    | exact resolve eq23059 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23059
  have eq23154 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq23091 X0
       have i₂ := eq22953
       grind)
    | exact superpose eq22953 eq23091
    | exact resolve eq23091 eq22953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22953 eq23091
  have eq24537 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23122 (σ x)
       grind)
    | exact superpose eq23122 eq16
    | exact resolve eq16 eq23122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23122
  have eq24562 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq24537
       have i₂ := eq23154 x
       grind)
    | exact superpose eq23154 eq24537
    | exact resolve eq24537 eq23154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23154 eq24537
  have eq24563 : False := by grind
  exact eq24563
